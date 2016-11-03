
open HolKernel boolLib bossLib Parse; val _ = new_theory "multiword";

val _ = set_trace "Unicode" 0;

open pred_setTheory res_quanTheory arithmeticTheory wordsLib wordsTheory bitTheory;
open pairTheory listTheory rich_listTheory relationTheory pairTheory integerTheory;
open fcpTheory lcsymtacs;
open ASCIInumbersTheory

val _ = numLib.prefer_num();

infix \\ val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val REV = Tactical.REVERSE;


(* general *)

val b2n_def = Define `(b2n T = 1) /\ (b2n F = 0:num)`;
val b2w_def = Define `b2w c = n2w (b2n c)`;

val MULT_ADD_LESS_MULT = Q.prove(
  `!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k:num`,
  REPEAT STRIP_TAC
  \\ `SUC m <= l` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ `m * j <= m * k` by ASM_SIMP_TAC bool_ss [LE_MULT_LCANCEL]
  \\ DECIDE_TAC);

val MULT_ADD_LESS_MULT_ADD = Q.prove(
  `!m n k l p. m < l /\ n < k /\ p < k ==> m * k + n < l * k + p:num`,
  REPEAT STRIP_TAC
  \\ `SUC m <= l` by ASM_REWRITE_TAC [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by ASM_SIMP_TAC bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ DECIDE_TAC);

val SPLIT_LET2 = prove(
  ``!x y z P. (let (x,y) = z in P x y (x,y)) =
              (let x = FST z in let y = SND z in P x y (x,y))``,
  Cases_on `z` \\ SIMP_TAC std_ss [LET_THM]);


(* multiword related general *)

val dimwords_def = Define `dimwords k n = (2:num) ** (k * dimindex n)`;

val k2mw_def = Define `
  (k2mw 0 n = []:('a word) list) /\
  (k2mw (SUC l) n = n2w n :: k2mw l (n DIV dimword(:'a)))`;

val mw2n_def = Define `
  (mw2n [] = 0) /\
  (mw2n (x::xs) = w2n (x:'a word) + dimword (:'a) * mw2n xs)`;

val mw2i_def = Define `
  (mw2i (F,xs) = (& (mw2n xs)):int) /\
  (mw2i (T,xs) = - & (mw2n xs))`;

val n2mw_def = tDefine "n2mw" `
  n2mw n = if n = 0 then []:'a word list else
             n2w (n MOD dimword (:'a)) :: n2mw (n DIV dimword(:'a))`
   (WF_REL_TAC `measure I`
    \\ SIMP_TAC std_ss [MATCH_MP DIV_LT_X ZERO_LT_dimword,ONE_LT_dimword]
    \\ DECIDE_TAC);

val n2mw_ind = fetch "-" "n2mw_ind"

val i2mw_def = Define `i2mw i = (i < 0,n2mw (Num (ABS i)))`;

val mw_ok_def = Define `mw_ok xs = ~(xs = []) ==> ~(LAST xs = 0w)`;

val n2mw_0 = Q.prove(`(n2mw 0 = [])`,METIS_TAC [n2mw_def]);
val n2mw_thm = Q.prove(
  `~(n = 0) ==> (n2mw n = (n2w (n MOD dimword (:'a)):'a word) ::
                           n2mw (n DIV dimword(:'a)))`,
  METIS_TAC [n2mw_def]);

val k2mw_SUC = REWRITE_CONV [k2mw_def] ``k2mw (SUC n) m``;

val ZERO_LT_dimwords = Q.prove(`!k. 0 < dimwords k (:'a)`,
  Cases \\ SIMP_TAC std_ss [dimwords_def,EVAL ``0<2``,ZERO_LT_EXP]);

val dimwords_SUC =
  (REWRITE_CONV [dimwords_def,MULT,EXP_ADD] THENC
   REWRITE_CONV [GSYM dimwords_def,GSYM dimword_def]) ``dimwords (SUC k) (:'a)``;

val dimwords_thm = Q.prove(
  `(dimwords 0 (:'a) = 1) /\
    (dimwords (SUC k) (:'a) = dimword (:'a) * dimwords k (:'a))`,
  FULL_SIMP_TAC std_ss [dimwords_def,MULT,EXP_ADD,dimword_def,AC MULT_COMM MULT_ASSOC]);

val mw_ok_CLAUSES = Q.prove(
  `mw_ok [] /\ (mw_ok (x::xs) = ((xs = []) ==> ~(x = 0w)) /\ mw_ok xs)`,
  SIMP_TAC std_ss [mw_ok_def,NOT_NIL_CONS]
  \\ `(xs = []) \/ ?y ys. xs = SNOC y ys` by METIS_TAC [SNOC_CASES]
  \\ ASM_SIMP_TAC std_ss [LAST_DEF,LAST_SNOC,NOT_SNOC_NIL]);

val k2mw_SNOC = Q.store_thm("k2mw_SNOC",
  `!k n. k2mw (SUC k) n = SNOC ((n2w (n DIV dimwords k (:'a))):'a word) (k2mw k n)`,
  Induct THEN1 REWRITE_TAC [k2mw_def,SNOC,dimwords_def,MULT_CLAUSES,EXP,DIV_1]
  \\ ONCE_REWRITE_TAC [k2mw_def] \\ ASM_REWRITE_TAC [SNOC]
  \\ SIMP_TAC bool_ss [dimwords_def,dimword_def,MULT,EXP_ADD,
       AC MULT_COMM MULT_ASSOC,DIV_DIV_DIV_MULT,EVAL ``0<2``,ZERO_LT_EXP,ZERO_LT_dimword]);

val k2mw_mw2n = Q.prove(
  `!xs. (k2mw (LENGTH xs) (mw2n xs) = xs)`,
  Induct THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,mw2n_def,k2mw_def,CONS_11]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases \\ FULL_SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ FULL_SIMP_TAC std_ss [MOD_MULT,DIV_MULT]);

val LENGTH_k2mw = Q.store_thm("LENGTH_k2mw",
  `!k n. LENGTH (k2mw k n) = k`,Induct \\ ASM_REWRITE_TAC [k2mw_def,LENGTH]);

val k2mw_mod = Q.prove(
  `!k m. k2mw k (m MOD dimwords k (:'a)):('a word) list = k2mw k m`,
  Induct \\ REWRITE_TAC [k2mw_def,dimwords_def,MULT,CONS_11]
  \\ REWRITE_TAC [GSYM dimwords_def,EXP_ADD,GSYM dimword_def]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ ASM_SIMP_TAC bool_ss [GSYM DIV_MOD_MOD_DIV,ZERO_LT_dimword,ZERO_LT_dimwords]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ ASM_SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords]);

val mw2n_APPEND = Q.prove(
  `!xs ys. mw2n (xs ++ ys) = mw2n xs + dimwords (LENGTH xs) (:'a) * mw2n (ys:'a word list)`,
  Induct \\ ASM_SIMP_TAC std_ss [dimwords_thm,LENGTH,APPEND,mw2n_def] \\ DECIDE_TAC);

val k2mw_APPEND = Q.prove(
  `!k l m n.
      k2mw k m ++ k2mw l n =
      k2mw (k+l) (m MOD dimwords k (:'a) + dimwords k (:'a) * n) :('a word) list`,
  Induct
  THEN1 REWRITE_TAC [k2mw_def,APPEND_NIL,ADD_CLAUSES,dimwords_def,MULT_CLAUSES,EXP,MOD_1]
  \\ ASM_REWRITE_TAC [ADD,k2mw_def,APPEND,CONS_11] \\ REPEAT STRIP_TAC THENL [
    ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ SIMP_TAC bool_ss [dimwords_SUC,MULT_ASSOC,n2w_11,MOD_TIMES,ZERO_LT_dimword]
    \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ SIMP_TAC bool_ss [MOD_MULT_MOD,ZERO_LT_dimword,ZERO_LT_dimwords],
    REWRITE_TAC [dimwords_SUC,DECIDE ``m+k*p*q:num=k*q*p+m``]
    \\ SIMP_TAC bool_ss [ADD_DIV_ADD_DIV,ZERO_LT_dimword,ZERO_LT_dimwords,DIV_MOD_MOD_DIV]
    \\ METIS_TAC [MULT_COMM,ADD_COMM]]);

val dimwords_ADD =
  (REWRITE_CONV [dimwords_def,RIGHT_ADD_DISTRIB,EXP_ADD] THENC
   REWRITE_CONV [GSYM dimwords_def]) ``dimwords (i+j) (:'a)``;

val TWO_dimwords_LE_dinwords_SUC = Q.prove(
  `!i. 2 * dimwords i (:'a) <= dimwords (SUC i) (:'a)`,
  REWRITE_TAC [dimwords_def,MULT,EXP_ADD] \\ STRIP_TAC
  \\ ASSUME_TAC (MATCH_MP LESS_OR DIMINDEX_GT_0)
  \\ Q.SPEC_TAC (`2 ** (i * dimindex (:'a))`,`x`)
  \\ IMP_RES_TAC LESS_EQUAL_ADD
  \\ ASM_REWRITE_TAC [EXP_ADD,EXP,MULT_CLAUSES,DECIDE ``n*(m*k)=m*n*k:num``]
  \\ `0 < 2**p` by ASM_REWRITE_TAC [ZERO_LT_EXP,EVAL ``0<2``]
  \\ REWRITE_TAC [RW [MULT_CLAUSES] (Q.SPECL [`m`,`1`] LE_MULT_LCANCEL)]
  \\ DECIDE_TAC);

val k2mw_MOD_ADD = Q.prove(
  `!i m n. k2mw i (m MOD dimwords i (:'a) + n) = k2mw i (m + n) :('a word)list`,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `m` (MATCH_MP DA (Q.SPEC `i` ZERO_LT_dimwords)))
  \\ ASM_SIMP_TAC bool_ss [GSYM ADD_ASSOC,MOD_MULT]
  \\ ONCE_REWRITE_TAC [GSYM k2mw_mod]
  \\ ASM_SIMP_TAC bool_ss [MOD_TIMES,ZERO_LT_dimwords]);

val mw2n_lt = Q.prove(
  `!xs. mw2n xs < dimwords (LENGTH (xs:'a word list)) (:'a)`,
  Induct \\ SIMP_TAC std_ss [NOT_NIL_CONS,LENGTH,dimwords_thm,mw2n_def]
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_SIMP_TAC std_ss [w2n_lt]);

val k2mw_EXISTS = Q.store_thm("k2mw_EXISTS",
  `!xs:('a word) list. ?k. (xs = k2mw (LENGTH xs) k) /\ k < dimwords (LENGTH xs) (:'a)`,
  Induct \\ REWRITE_TAC [k2mw_def,LENGTH]
  THEN1 (Q.EXISTS_TAC `0` \\ REWRITE_TAC [dimwords_def,EXP,MULT_CLAUSES] \\ EVAL_TAC)
  \\ POP_ASSUM (STRIP_ASSUME_TAC o GSYM) \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `k * dimword (:'a) + w2n h`
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ ASM_SIMP_TAC bool_ss [DIV_MULT,w2n_lt,MOD_MULT,n2w_w2n,dimwords_SUC]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ ASM_REWRITE_TAC [w2n_lt,LESS_EQ_REFL]);

val mw2n_MAP_ZERO = Q.prove(
  `!xs ys. mw2n (xs ++ MAP (\x.0w) ys) = mw2n xs`,
  Induct THEN1 (SIMP_TAC std_ss [APPEND] \\ Induct
    \\ FULL_SIMP_TAC std_ss [MAP,mw2n_def,w2n_n2w,ZERO_LT_dimword])
  \\ ASM_SIMP_TAC std_ss [APPEND,mw2n_def]);

val EXISTS_k2mw = Q.prove(
  `!(xs:'a word list).
      ?n k. (xs = k2mw k n) /\ (LENGTH xs = k) /\ n < dimwords k (:'a)`,
  Induct \\ FULL_SIMP_TAC std_ss [k2mw_def,LENGTH,CONS_11] \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ SIMP_TAC std_ss [ZERO_LT_dimwords])
  \\ Q.EXISTS_TAC `n * dimword (:'a) + w2n h`
  \\ ASM_SIMP_TAC std_ss [MATCH_MP DIV_MULT (SPEC_ALL w2n_lt)]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ SIMP_TAC std_ss [MATCH_MP MOD_TIMES ZERO_LT_dimword]
  \\ SIMP_TAC std_ss [n2w_mod,n2w_w2n,dimwords_thm]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [MULT_COMM]))
  \\ ONCE_REWRITE_TAC [MULT_COMM] \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
  \\ ASM_SIMP_TAC std_ss [w2n_lt]);

val mw2n_k2mw = Q.prove(
  `!k n. n < dimwords k (:'a) ==> (mw2n ((k2mw k n):'a word list) = n)`,
  Induct \\ SIMP_TAC std_ss [dimwords_thm,DECIDE ``n<1 = (n = 0)``,
   k2mw_def,mw2n_def,RW1[MULT_COMM](GSYM DIV_LT_X),ZERO_LT_dimwords,ZERO_LT_dimword]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ METIS_TAC [DIVISION,ZERO_LT_dimword,ADD_COMM,MULT_COMM]);

val mw2n_gt = Q.prove(
  `!xs. mw_ok xs /\ ~(xs = []) ==> dimwords (LENGTH xs - 1) (:'a) <= mw2n (xs:'a word list)`,
  Induct \\ SIMP_TAC std_ss [NOT_NIL_CONS,LENGTH,ADD1,mw2n_def]
  \\ Cases_on `xs` THEN1
   (SIMP_TAC std_ss [mw_ok_def,LAST_CONS,NOT_NIL_CONS,LENGTH,mw2n_def,dimwords_thm]
    \\ Cases_word \\ ASM_SIMP_TAC std_ss [n2w_11,w2n_n2w,ZERO_LT_dimword] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [NOT_NIL_CONS] \\ REPEAT STRIP_TAC
  \\ `mw_ok (h::t)` by FULL_SIMP_TAC std_ss [mw_ok_def,LAST_CONS,NOT_NIL_CONS]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH,dimwords_thm,mw2n_def]
  \\ `0 < dimword (:'a)` by METIS_TAC [ZERO_LT_dimword]
  \\ `~(dimword (:'a) = 0)` by DECIDE_TAC
  \\ MATCH_MP_TAC (DECIDE ``m <= k ==> m <= n + k:num``)
  \\ ASM_SIMP_TAC std_ss [LE_MULT_LCANCEL]);

val mw2n_LESS = Q.store_thm("mw2n_LESS",
  `!(xs:'a word list) (ys:'a word list).
       mw_ok xs /\ mw_ok ys /\ mw2n xs <= mw2n ys ==> LENGTH xs <= LENGTH ys`,
  REPEAT STRIP_TAC \\ Cases_on `xs = []` \\ ASM_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `ys = []` THEN1
   (IMP_RES_TAC mw2n_gt
    \\ `0 < dimwords (LENGTH xs - 1) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
    \\ FULL_SIMP_TAC std_ss [LENGTH,mw2n_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC mw2n_gt
  \\ `mw2n xs < dimwords (LENGTH xs) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `mw2n ys < dimwords (LENGTH ys) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `dimwords (LENGTH xs - 1) (:'a) < dimwords (LENGTH ys) (:'a)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [dimwords_def] \\ DECIDE_TAC);

val mw_ok_n2mw = Q.store_thm("mw_ok_n2mw",
  `!n. mw_ok ((n2mw n):'a word list)`,
  HO_MATCH_MP_TAC n2mw_ind \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [n2mw_def]
  \\ Cases_on `n = 0` THEN1 ASM_SIMP_TAC std_ss [mw_ok_def] \\ RES_TAC
  \\ Cases_on `n < dimword (:'a)` \\ ASM_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]
  THEN1 (ONCE_REWRITE_TAC [n2mw_def]
    \\ ASM_SIMP_TAC std_ss [mw_ok_def,LAST_DEF,n2w_11,ZERO_LT_dimword])
  \\ FULL_SIMP_TAC std_ss [mw_ok_def,NOT_NIL_CONS,LAST_DEF]
  \\ REV (`~(n2mw (n DIV dimword (:'a)) = ([]:'a word list))` by ALL_TAC)
  THEN1 METIS_TAC []
  \\ `0 < n DIV dimword (:'a)` by (FULL_SIMP_TAC std_ss [X_LT_DIV,ZERO_LT_dimword] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [n2mw_def] \\ FULL_SIMP_TAC std_ss [DECIDE ``0<n = ~(n = 0)``]
  \\ FULL_SIMP_TAC std_ss [NOT_NIL_CONS]);

val mw_ok_i2mw = store_thm("mw_ok_i2mw",
  ``!i x xs. (i2mw i = (x,xs)) ==> mw_ok xs``,
  SIMP_TAC std_ss [i2mw_def,mw_ok_n2mw]);

val n2mw_EQ_k2mw = Q.prove(
  `!n. n2mw n = k2mw (LENGTH ((n2mw n):'a word list)) n :'a word list`,
  HO_MATCH_MP_TAC n2mw_ind \\ REPEAT STRIP_TAC \\ Cases_on `n = 0`
  \\ FULL_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [n2mw_def]
  \\ ASM_SIMP_TAC std_ss [LENGTH,k2mw_def,CONS_11,n2w_11,MOD_MOD,ZERO_LT_dimword]);

val LESS_dimwords_n2mw = Q.prove(
  `!n. n < dimwords (LENGTH ((n2mw n):'a word list)) (:'a)`,
  HO_MATCH_MP_TAC n2mw_ind \\ REPEAT STRIP_TAC \\ Cases_on `n = 0`
  \\ FULL_SIMP_TAC std_ss [ZERO_LT_dimwords] \\ ONCE_REWRITE_TAC [n2mw_def]
  \\ ASM_SIMP_TAC std_ss [LENGTH,dimwords_SUC]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [MATCH_MP DIVISION ZERO_LT_dimword]))
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
  \\ ASM_SIMP_TAC std_ss [ZERO_LT_dimword,MOD_LESS]);

val mw2n_n2mw = Q.store_thm("mw2n_n2mw",
  `!n. mw2n (n2mw n) = n`,
  ONCE_REWRITE_TAC [n2mw_EQ_k2mw] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC mw2n_k2mw \\ ASM_SIMP_TAC std_ss [LESS_dimwords_n2mw]);

val mw2i_i2mw = Q.store_thm("mw2i_i2mw",
  `!i. mw2i (i2mw i) = i`,
  REPEAT STRIP_TAC \\ Cases_on `i < 0` \\ ASM_SIMP_TAC std_ss [mw2i_def,i2mw_def]
  \\ ASM_SIMP_TAC std_ss [INT_ABS,mw2n_n2mw] \\ intLib.COOPER_TAC);

val n2mw_11 = Q.store_thm("n2mw_11",
  `!m n. (n2mw m = n2mw n) = (m = n)`,
  HO_MATCH_MP_TAC n2mw_ind
  \\ REPEAT STRIP_TAC \\ Cases_on `m = 0` \\ Cases_on `n = 0`
  \\ ONCE_REWRITE_TAC [n2mw_def] \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,CONS_11]
  \\ Cases_on `m = n` \\ ASM_SIMP_TAC std_ss []
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ METIS_TAC [DIVISION,ZERO_LT_dimword]);

val i2mw_11 = Q.store_thm("i2mw_11",
  `!i j. (i2mw i = i2mw j) = (i = j)`,
  SIMP_TAC std_ss [i2mw_def,n2mw_11] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss [] \\ intLib.COOPER_TAC);

val mw_ok_IMP_EXISTS_n2mw = Q.prove(
  `!xs. mw_ok xs ==> ?n. xs = n2mw n`,
  Induct THEN1 METIS_TAC [n2mw_def] \\ SIMP_TAC std_ss [mw_ok_CLAUSES]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `n * dimword (:'a) + w2n h`
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [n2mw_def]))
  \\ SIMP_TAC std_ss [DIV_MULT,w2n_lt,MOD_MULT,n2w_w2n,
       MATCH_MP (DECIDE ``0<n ==> ~(n = 0)``) ZERO_LT_dimword]
  \\ Cases_on `n = 0` \\ ASM_SIMP_TAC std_ss []
  \\ `xs = []` by METIS_TAC [n2mw_def] \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `h <> 0w` MP_TAC \\ Q.SPEC_TAC (`h`,`h`) \\ Cases
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,w2n_n2w]);

val IMP_EQ_n2mw = Q.prove(
  `!xs i. mw_ok xs /\ (mw2n xs = i) ==> (xs = n2mw i)`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC mw_ok_IMP_EXISTS_n2mw
  \\ FULL_SIMP_TAC std_ss [n2mw_11,mw2n_n2mw]);

val IMP_EQ_n2mw_ALT = Q.prove(
  `!xs ys. mw_ok xs /\ mw_ok ys /\ (mw2n xs = mw2n ys) ==> (xs = ys)`,
  METIS_TAC [IMP_EQ_n2mw]);

val EXISTS_i2mw = prove(
  ``!x. mw_ok (SND x) /\ ~(x = (T,[])) ==> ?y. x = i2mw y``,
  Cases \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC mw_ok_IMP_EXISTS_n2mw THEN1
   (Q.EXISTS_TAC `(& n)` \\ ASM_SIMP_TAC std_ss [i2mw_def,n2mw_11]
    \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ intLib.COOPER_TAC)
  \\ `~(n = 0)` by METIS_TAC [n2mw_def]
  \\ Q.EXISTS_TAC `if q then -(& n) else (& n)` \\ POP_ASSUM MP_TAC
  \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [i2mw_def,n2mw_11]
  \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ intLib.COOPER_TAC);

val mw2i_EQ_IMP_EQ_i2mw = prove(
  ``!x. mw_ok (SND x) /\ ~(x = (T,[])) /\ (mw2i x = i) ==> (x = i2mw i)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_i2mw \\ FULL_SIMP_TAC std_ss [mw2i_i2mw]);

val LENGTH_n2mw_LESS_LENGTH_n2mw = Q.prove(
  `!m n. m <= n ==>
          LENGTH (n2mw m:'a word list) <= LENGTH (n2mw n:'a word list)`,
  HO_MATCH_MP_TAC n2mw_ind
  \\ REPEAT STRIP_TAC \\ Cases_on `m = 0` \\ Cases_on `n = 0`
  \\ ONCE_REWRITE_TAC [n2mw_def] \\ ASM_SIMP_TAC std_ss [LENGTH] THEN1 DECIDE_TAC
  \\ REV (`m DIV dimword (:'a) <= n DIV dimword (:'a)` by ALL_TAC) THEN1 METIS_TAC []
  \\ SIMP_TAC std_ss [X_LE_DIV,ZERO_LT_dimword]
  \\ MATCH_MP_TAC (DECIDE ``!p. m + p <= n ==> m <= n``)
  \\ Q.EXISTS_TAC `m MOD dimword (:'a)`
  \\ ASM_SIMP_TAC std_ss [GSYM DIVISION,ZERO_LT_dimword]);

val mw2n_EQ_IMP_EQ = Q.prove(
  `!xs ys. (LENGTH xs = LENGTH ys) /\ (mw2n xs = mw2n ys) ==> (xs = ys)`,
  REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `xs` EXISTS_k2mw)
  \\ STRIP_ASSUME_TAC (Q.SPEC `ys` EXISTS_k2mw)
  \\ FULL_SIMP_TAC std_ss [mw2n_k2mw]);

(* fix and zerofix *)

val mw_fix_def = tDefine "mw_fix" `
  mw_fix xs = if xs = [] then [] else
                   if LAST xs = 0w then mw_fix (BUTLAST xs) else xs`
  (WF_REL_TAC `measure LENGTH` \\ Cases
   \\ SIMP_TAC std_ss [LENGTH_BUTLAST,NOT_NIL_CONS,LENGTH]);

val mw_fix_ind = fetch "-" "mw_fix_ind"

val mw_zerofix_def = Define `
  mw_zerofix x = if x = (T,[]) then (F,[]) else x`;

val mw_ok_mw_fix = Q.store_thm("mw_ok_fix",
  `!xs. mw_ok (mw_fix xs)`,
  HO_MATCH_MP_TAC mw_fix_ind \\ Cases \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_fix_def]
  \\ FULL_SIMP_TAC std_ss [mw_ok_CLAUSES,NOT_CONS_NIL]
  \\ Cases_on `LAST (h::t) = 0w` \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [mw_ok_def]);

val mw_ok_mw_fix_ID = Q.store_thm("mw_ok_mw_fix_ID",
  `!xs. mw_ok xs ==> (mw_fix xs = xs)`,
  Cases \\ ASM_SIMP_TAC std_ss [mw_ok_def,Once mw_fix_def,NOT_NIL_CONS]);

val mw2n_mw_fix = Q.prove(
  `!xs. mw2n (mw_fix xs) = mw2n xs`,
  HO_MATCH_MP_TAC mw_fix_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_fix_def]
  \\ `(xs = []) \/ ?y ys. xs = SNOC y ys` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ Cases_on `y = 0w` \\ ASM_SIMP_TAC std_ss [SNOC_APPEND]
  \\ ASM_SIMP_TAC std_ss [mw2n_APPEND,mw2n_def,w2n_n2w,ZERO_LT_dimword]);

val mw2i_mw_zerofix = Q.prove(
  `!x. mw2i (mw_zerofix x) = mw2i x`,
  SRW_TAC [] [mw_zerofix_def,mw2i_def,mw2n_def]);

val mw_zerofix_thm = prove(
  ``!x b xs. ~(mw_zerofix x = (T,[])) /\ mw_ok (SND (mw_zerofix (b, mw_fix xs)))``,
  SRW_TAC [] [mw_zerofix_def,mw_ok_CLAUSES,mw_ok_mw_fix]);

val mw_fix_NIL = Q.store_thm("mw_fix_NIL",
  `!xs. (mw_fix xs = []) = (mw2n xs = 0)`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_fix_def]
  \\ SIMP_TAC std_ss [mw2n_def,NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ Cases_on `x = 0w` \\ ASM_SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def]
  \\ ASM_SIMP_TAC std_ss [w2n_n2w,ZERO_LT_dimword,GSYM SNOC_APPEND,NOT_SNOC_NIL]
  \\ `0 < dimwords (LENGTH xs) (:'a)` by METIS_TAC [ZERO_LT_dimwords] \\ DISJ2_TAC
  \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC \\ Cases_on `x`
  \\ FULL_SIMP_TAC std_ss [n2w_11,w2n_n2w,ZERO_LT_dimword]);

val mw_fix_LENGTH_ZERO = Q.prove(
  `!xs. (LENGTH (mw_fix xs) = 0) = (mw2n xs = 0)`,
  FULL_SIMP_TAC std_ss [LENGTH_NIL,mw_fix_NIL]);

val mw_fix_EQ_n2mw =
  Q.SPEC `mw_fix xs` mw_ok_IMP_EXISTS_n2mw |> RW [mw_ok_mw_fix] |> GEN_ALL;

val n2mw_mw2n = Q.prove(
  `!xs. (mw_fix xs = n2mw (mw2n xs))`,
  REPEAT STRIP_TAC
  \\ `?n. mw_fix xs = n2mw n` by METIS_TAC [mw_fix_EQ_n2mw]
  \\ ONCE_REWRITE_TAC [GSYM mw2n_mw_fix] \\ FULL_SIMP_TAC std_ss [mw2n_n2mw]);

val mw_ok_mw_mw2n = Q.prove(
  `!xs. mw_ok xs ==> (xs = n2mw (mw2n xs))`,
  METIS_TAC [n2mw_mw2n,mw_ok_mw_fix,mw_ok_mw_fix_ID]);

val LENGTH_mw_fix = Q.store_thm("LENGTH_mw_fix",
  `!xs. LENGTH (mw_fix xs) <= LENGTH xs`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once mw_fix_def] \\ SRW_TAC [] []
  \\ DECIDE_TAC);

val REPLICATE_SNOC = Q.store_thm("REPLICATE_SNOC",
  `!n x. REPLICATE (SUC n) x = SNOC x (REPLICATE n x)`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE]);

val mw_fix_thm = Q.store_thm("mw_fix_thm",
  `!xs. mw_fix xs ++ REPLICATE (LENGTH xs - LENGTH (mw_fix xs)) 0x0w = xs`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC THEN1 EVAL_TAC
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_fix_def]
  \\ FULL_SIMP_TAC std_ss [NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ Cases_on `x = 0w` \\ FULL_SIMP_TAC std_ss [EVAL ``REPLICATE 0 x``,APPEND_NIL]
  \\ `REPLICATE (LENGTH (SNOC 0x0w xs) - LENGTH (mw_fix xs)) (0x0w:'a word) =
      SNOC 0w (REPLICATE (LENGTH xs - LENGTH (mw_fix xs)) 0x0w)` by ALL_TAC THEN1
   (`LENGTH (SNOC 0x0w xs) - LENGTH (mw_fix xs) =
     SUC (LENGTH xs - LENGTH (mw_fix xs))` by ALL_TAC THEN1
     (`LENGTH (mw_fix xs) <= LENGTH xs` by METIS_TAC [LENGTH_mw_fix]
      \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [REPLICATE_SNOC])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND_ASSOC]);

val mw2n_REPLICATE = Q.prove(
  `!n. mw2n (REPLICATE n 0x0w) = 0`,
  Induct THEN1 EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [REPLICATE,mw2n_def,w2n_n2w,ZERO_LT_dimword]);

(* add/sub *)

val single_add_def = Define `
  single_add (x:'a word) (y:'a word) c =
    (x + y + b2w c, dimword (:'a) <= w2n x + w2n y + b2n c)`;

val mw_add_def = Define `
  (mw_add [] ys c = ([],c)) /\
  (mw_add (x::xs) ys c =
    let (z,c1) = single_add x (HD ys) c in
    let (zs,c2) = mw_add xs (TL ys) c1 in (z::zs,c2))`;

val single_sub_def = Define `
  single_sub (x:'a word) (y:'a word) c = single_add x (~y) c`;

val mw_sub_def = Define `
  (mw_sub [] ys c = ([],c)) /\
  (mw_sub (x::xs) [] c =
    let (z,c1) = single_sub x 0w c in
    let (zs,c2) = mw_sub xs [] c1 in (z::zs,c2)) /\
  (mw_sub (x::xs) (y::ys) c =
    let (z,c1) = single_sub x y c in
    let (zs,c2) = mw_sub xs ys c1 in (z::zs,c2))`;

val single_add_thm = store_thm("single_add_thm",
  ``!(x:'a word) y z c d.
      (single_add x y c = (z,d)) ==>
      (w2n z + dimword (:'a) * b2n d = w2n x + w2n y + b2n c)``,
  NTAC 2 Cases_word \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [single_add_def,w2n_n2w,LESS_MOD,b2w_def] \\ STRIP_TAC
  \\ Cases_on `dimword (:'a) <= n + n' + b2n c`
  \\ FULL_SIMP_TAC std_ss [word_add_n2w,GSYM NOT_LESS,w2n_n2w,b2n_def]
  \\ REV (`(n + n' + b2n c) DIV dimword (:'a) = 1` by ALL_TAC)
  THEN1 METIS_TAC [DIVISION,MULT_CLAUSES,ADD_COMM,ZERO_LT_dimword]
  \\ `b2n c < 2` by (Cases_on `c` \\ SIMP_TAC std_ss [b2n_def])
  \\ `n + n' + b2n c - dimword (:'a) < dimword (:'a)` by DECIDE_TAC
  \\ `n + n' + b2n c = dimword (:'a) + (n + n' + b2n c - dimword (:'a))` by DECIDE_TAC
  \\ METIS_TAC [bitTheory.DIV_MULT_1]);

val b2n_thm = Q.prove(
  `!c. b2n c = if c then 1 else 0`,
  Cases \\ SIMP_TAC std_ss [b2n_def]);

val single_add_eq = store_thm("single_add_eq",
  ``single_add x y c = (FST (add_with_carry (x,y:'a word,c)),
                        FST (SND (add_with_carry (x,y,c))))``,
  SIMP_TAC std_ss [single_add_def,add_with_carry_def,LET_DEF,GSYM b2n_thm]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,n2w_w2n,b2w_def]
  \\ Cases_on `x` \\ Cases_on `y` \\ ASM_SIMP_TAC std_ss [w2n_n2w,LESS_MOD]
  \\ SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
  \\ Cases_on `n + n' + b2n c < dimword (:'a)`
  \\ ASM_SIMP_TAC std_ss [LESS_MOD,DECIDE ``(n <= m) = ~(m < n:num)``]
  \\ CONV_TAC ((RAND_CONV o RAND_CONV)
       (ONCE_REWRITE_CONV [MATCH_MP DIVISION ZERO_LT_dimword]))
  \\ SIMP_TAC std_ss [DECIDE ``((m = n + m:num) = (0 = n)) /\ (~(n=0)=0<n)``]
  \\ SIMP_TAC std_ss [X_LT_DIV,ZERO_LT_dimword] \\ DECIDE_TAC);

val mw_add_thm = prove(
  ``!xs ys c (zs:'a word list) d.
      (mw_add xs ys c = (zs,d)) /\ (LENGTH xs = LENGTH ys) ==>
      (mw2n zs + dimwords (LENGTH xs) (:'a) * b2n d =
       mw2n xs + mw2n ys + b2n c)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss
    [mw_add_def,LENGTH,dimwords_thm,mw2n_def,DECIDE ``~(SUC n = 0)``,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC
  \\ Q.PAT_X_ASSUM `bb = (zs,d)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ IMP_RES_TAC single_add_thm
  \\ Q.PAT_X_ASSUM `!ys. bbb` (MP_TAC o RW [] o Q.SPECL [`t`,`c1`])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,GSYM LEFT_ADD_DISTRIB,GSYM MULT_ASSOC]
  \\ DECIDE_TAC);

val single_sub_thm = prove(
  ``!(x:'a word) y z c d.
      (single_sub x y c = (z,d)) ==>
      (w2n z + dimword (:'a) * b2n d + w2n y = w2n x + b2n c + (dimword(:'a) - 1))``,
  SIMP_TAC std_ss [single_sub_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC single_add_thm \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [DECIDE ``(x+yy+c+y=x+c+d)=(yy+y=d:num)``]
  \\ Q.SPEC_TAC (`y`,`y`) \\ Cases
  \\ `dimword (:'a) - 1 - n < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [w2n_n2w,word_1comp_n2w] \\ DECIDE_TAC);

val mw_sub_lemma = prove(
  ``!xs ys c (zs:'a word list) d.
      (mw_sub xs ys c = (zs,d)) /\ (LENGTH xs = LENGTH ys) ==>
      (mw2n zs + mw2n ys + dimwords (LENGTH xs) (:'a) * b2n d =
       mw2n xs + b2n c + (dimwords (LENGTH xs) (:'a) - 1)) /\
      (LENGTH zs = LENGTH xs)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss
    [mw_sub_def,LENGTH,dimwords_thm,mw2n_def,DECIDE ``~(SUC n = 0)``,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC \\ IMP_RES_TAC single_sub_thm
  \\ Q.PAT_X_ASSUM `bb = (zs,d)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ Q.PAT_X_ASSUM `!ys. bbb` (MP_TAC o RW [] o Q.SPECL [`t`,`c1`])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [DECIDE ``z+d*zs+(h+d*t)+d*kk*c2 = z+h+d*zs+d*t+d*kk*c2:num``]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,GSYM LEFT_ADD_DISTRIB,GSYM MULT_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC,MULT_ASSOC,LENGTH]
  \\ ASM_SIMP_TAC std_ss [DECIDE ``z+h+d*xs+d*c1+dd:num = (z+d*c1+h)+d*xs+dd``]
  \\ `0 < dimwords (LENGTH t) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
  \\ Cases_on `dimwords (LENGTH t) (:'a)` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  \\ `0 < dimword (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimword] \\ DECIDE_TAC);

val mw_sub_thm = Q.prove(
  `!xs ys c zs d.
     (LENGTH xs = LENGTH ys) /\ mw2n ys <= mw2n xs ==>
     (mw2n (FST (mw_sub xs ys T)) = mw2n xs - mw2n ys)`,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
  \\ `?zs d. mw_sub xs ys T = (zs,d)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC mw_sub_lemma \\ ASM_SIMP_TAC std_ss []
  \\ `0 < dimwords (LENGTH xs) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
  \\ Cases_on `d` \\ FULL_SIMP_TAC std_ss [b2n_def] THEN1 DECIDE_TAC
  \\ `mw2n zs + mw2n ys = mw2n xs + dimwords (LENGTH xs) (:'a)` by DECIDE_TAC
  \\ `mw2n zs < dimwords (LENGTH xs) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `mw2n ys < dimwords (LENGTH xs) (:'a)` by METIS_TAC [mw2n_lt]
  \\ `F` by DECIDE_TAC);

val mw_addv_def = Define `
  (mw_addv [] ys c = if c then [1w] else []) /\
  (mw_addv (x::xs) ys c =
    let (y,ys2) = if ys = [] then (0w,ys) else (HD ys, TL ys) in
    let (z,c1) = single_add x y c in
      z :: mw_addv xs ys2 c1)`;

val WORD_NOT_ZERO_ONE = Q.prove(
  `~(0w = 1w)`,
  SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,ONE_LT_dimword]);

val mw_addv_thm = Q.prove(
  `!xs (ys:'a word list) c.
      (LENGTH ys <= LENGTH xs) ==>
      (mw2n (mw_addv xs ys c) = mw2n xs + mw2n ys + b2n c)`,
  Induct \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH] THEN1
   (Cases_on `c` \\ SIMP_TAC std_ss [mw_addv_def,b2n_def,
      mw2n_def,w2n_n2w,ONE_LT_dimword,mw_ok_def,LAST_DEF])
  \\ SIMP_TAC std_ss [mw_addv_def,LET_DEF] \\ REPEAT STRIP_TAC THEN1
   (POP_ASSUM (ASSUME_TAC o Q.SPEC `[]`) \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ `?z3 c3. single_add h 0w c = (z3,c3)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC single_add_thm
    \\ FULL_SIMP_TAC std_ss [mw2n_def,w2n_n2w,ZERO_LT_dimword] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [HD,TL,NOT_CONS_NIL]
  \\ `?z3 c3. single_add h' h c = (z3,c3)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC single_add_thm \\ FULL_SIMP_TAC std_ss [mw2n_def] \\ DECIDE_TAC);

val mw_ok_addv = Q.prove(
  `!xs ys c. mw_ok xs /\ mw_ok ys ==> mw_ok (mw_addv xs (ys:'a word list) c)`,
  Induct THEN1 (Cases_on `c`
    \\ SIMP_TAC std_ss [mw_addv_def,mw_ok_def,LAST_DEF,WORD_NOT_ZERO_ONE])
  \\ SIMP_TAC std_ss [mw_addv_def,SPLIT_LET2] \\ SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mw_ok_CLAUSES] \\ NTAC 4 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `ys2 = SND (if ys = [] then (0w,[]) else (HD ys,TL (ys:'a word list)))`
  \\ `mw_ok ys2` by ALL_TAC THEN1 (Q.UNABBREV_TAC `ys2`
     \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,TL,mw_ok_CLAUSES])
  \\ FULL_SIMP_TAC std_ss []
  \\ REV (Cases_on `xs`) \\ FULL_SIMP_TAC std_ss [mw_addv_def,SPLIT_LET2]
  \\ SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL]
  \\ Q.ABBREV_TAC `h2 = FST (if ys = [] then (0w,[]) else (HD ys,TL ys))`
  \\ Q.PAT_X_ASSUM `h <> 0w` MP_TAC \\ Q.SPEC_TAC (`h`,`h`) \\ Cases
  \\ ASM_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ `?z d. single_add (n2w n) h2 c = (z,d)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC single_add_thm
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [w2n_n2w]
  \\ Cases_on `d` \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL,b2n_def]
  \\ Q.SPEC_TAC (`z`,`z`) \\ Cases
  \\ ASM_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,w2n_n2w]);

val mw_addv_EQ_mw_add = store_thm("mw_addv_EQ_mw_add",
  ``!xs1 xs2 ys c1.
      (LENGTH ys = LENGTH xs1) ==>
      (mw_addv (xs1 ++ xs2) ys c1 =
        let (zs1,c2) = mw_add xs1 ys c1 in
        let (zs2,c3) = mw_add xs2 (MAP (\x.0w) xs2) c2 in
          zs1 ++ zs2 ++ if c3 then [1w] else [])``,
  Induct THEN1
   (Induct \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,LENGTH_NIL,mw_addv_def,mw_add_def]
    THEN1 SIMP_TAC std_ss [LET_DEF,APPEND] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [MAP,HD,TL,LET_DEF] \\ Cases_on `single_add h 0x0w c1`
    \\ FULL_SIMP_TAC std_ss [APPEND]
    \\ `?ts t. mw_add xs2 (MAP (\x. 0x0w) xs2) r = (ts,t)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [APPEND])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,LENGTH_NIL,mw_addv_def,mw_add_def,
       NOT_NIL_CONS,LET_DEF,TL,HD] \\ REPEAT STRIP_TAC
  \\ Cases_on `single_add h' h c1` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `mw_add xs1 t r` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `mw_add xs2 (MAP (\x. 0x0w) xs2) r'`
  \\ ASM_SIMP_TAC std_ss [APPEND]);

val mw_sub_APPEND = store_thm("mw_sub_APPEND",
  ``!xs1 xs2 ys c.
      (LENGTH xs1 = LENGTH ys) ==>
      (mw_sub (xs1 ++ xs2) ys c =
       let (ts1,c) = mw_sub xs1 ys c in
       let (ts2,c) = mw_sub xs2 [] c in
         (ts1 ++ ts2,c))``,
  Induct \\ Cases_on `ys`
  \\ ASM_SIMP_TAC std_ss [mw_sub_def,APPEND,LET_DEF,LENGTH,ADD1]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ ASM_SIMP_TAC std_ss [CONS_11,APPEND]);

val mw_subv_def = Define `
  mw_subv xs ys = mw_fix (FST (mw_sub xs ys T))`;

val mw_sub_SNOC_0 = Q.prove(
  `!xs ys c. mw_sub xs (SNOC 0w ys) c = mw_sub xs ys c`,
  Induct \\ SIMP_TAC std_ss [mw_sub_def] \\ Cases_on `ys`
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND,mw_sub_def]);

val mw_sub_APPEND_0 = Q.prove(
  `!n xs ys c. mw_sub xs (ys ++ REPLICATE n 0w) c = mw_sub xs ys c`,
  Induct \\ ASM_SIMP_TAC std_ss [REPLICATE_SNOC,APPEND_SNOC,mw_sub_SNOC_0]
  \\ SIMP_TAC std_ss [REPLICATE,APPEND_NIL]);

val mw_sub_mw_fix = Q.store_thm("mw_sub_mw_fix",
  `!xs ys. mw_sub xs (mw_fix ys) c = mw_sub xs (ys:'a word list) c`,
  METIS_TAC [mw_sub_APPEND_0,mw_fix_thm]);

val mw2n_APPEND_REPLICATE = Q.prove(
  `!ys n. mw2n ys = mw2n (ys ++ REPLICATE n 0w)`,
  SIMP_TAC std_ss [mw2n_APPEND,mw2n_REPLICATE]);

val mw_subv_thm = Q.prove(
  `!xs ys. mw2n ys <= mw2n xs /\ (LENGTH ys <= LENGTH xs) ==>
            (mw2n (mw_subv xs ys) = mw2n xs - mw2n ys)`,
  SIMP_TAC std_ss [mw_subv_def,mw2n_mw_fix] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [(GSYM mw_sub_APPEND_0)
       |> Q.SPECL [`(LENGTH (xs:'a word list) - LENGTH (ys:'a word list))`,
                   `xs`,`ys`,`T`]] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASSUME_TAC (Q.SPECL [`ys`,
     `(LENGTH (xs:'a word list) - LENGTH (ys:'a word list))`] mw2n_APPEND_REPLICATE)
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
  \\ MATCH_MP_TAC (GSYM mw_sub_thm) \\ FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [GSYM mw2n_APPEND_REPLICATE,LENGTH_APPEND,LENGTH_REPLICATE]
  \\ DECIDE_TAC);

val mwi_add_def = Define `
  mwi_add (s,xs) (t,ys) =
    if s = t then
      if LENGTH ys <= LENGTH xs then (s, mw_addv xs ys F) else (s, mw_addv ys xs F)
    else
      if mw2n ys = mw2n xs then (F,[]) else
      if mw2n ys <= mw2n xs then (s,mw_subv xs ys) else (~s,mw_subv ys xs)`;

val mwi_sub_def = Define `
  mwi_sub (s,xs) (t,ys) = mwi_add (s,xs) (~t,ys)`;

val mwi_add_lemma = prove(
  ``!s t xs ys.
      mw_ok xs /\ mw_ok ys ==>
      (mw2i (mwi_add (s,xs) (t,ys)) = mw2i (s,xs) + mw2i (t,ys))``,
  REPEAT STRIP_TAC \\ Cases_on `s` \\ Cases_on `t` \\ Cases_on `mw2n ys <= mw2n xs`
  \\ Cases_on `LENGTH ys <= LENGTH xs`
  \\ IMP_RES_TAC (DECIDE ``~(m<=n) ==> n <= m:num``)
  \\ IMP_RES_TAC mw2n_LESS \\ Cases_on `mw2n xs = mw2n ys`
  \\ IMP_RES_TAC (DECIDE ``m<=n/\~(m=n) ==> ~(n<=m:num)``)
  \\ FULL_SIMP_TAC std_ss [mwi_add_def,mw2i_def,mw_addv_thm,INT_ADD_CALCULATE,
       AC ADD_COMM ADD_ASSOC,mw_subv_thm,INT_ADD_REDUCE,mw2n_def,b2n_def]);

val mwi_add_lemma2 = RW [mw_ok_n2mw,GSYM i2mw_def,mw2i_i2mw]
  (Q.SPECL [`i<0:int`,`j<0:int`,`n2mw (Num (ABS i))`,`n2mw (Num (ABS j))`] mwi_add_lemma);

val mw_addv_IMP_NIL = Q.prove(
  `!xs ys. (mw_addv xs ys c = []) ==> (xs = [])`,
  Induct \\ SIMP_TAC std_ss [mw_addv_def,SPLIT_LET2]
  \\ SIMP_TAC std_ss [LET_DEF,NOT_CONS_NIL]);

val n2mw_NIL = Q.store_thm("n2mw_NIL",
  `!n. (n2mw n = []) = (n = 0)`,
  REPEAT STRIP_TAC \\ Cases_on `n = 0` \\ ONCE_REWRITE_TAC [n2mw_def]
  \\ ASM_SIMP_TAC std_ss [NOT_CONS_NIL]);

val mwi_add_thm = Q.store_thm("mwi_add_thm",
  `!i j. mwi_add (i2mw i) (i2mw j) = i2mw (i + j)`,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC mw2i_EQ_IMP_EQ_i2mw
  \\ FULL_SIMP_TAC std_ss [mwi_add_lemma2]
  \\ SIMP_TAC std_ss [mwi_add_def,i2mw_def,mw2n_n2mw] \\ STRIP_TAC
  THEN1 SRW_TAC [] [mw_ok_addv,mw_ok_n2mw,mw_subv_def,mw_ok_mw_fix,mw_ok_CLAUSES]
  \\ SRW_TAC [] [] \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_addv_IMP_NIL \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  THEN1 (FULL_SIMP_TAC std_ss [mw_addv_def,n2mw_NIL] \\ intLib.COOPER_TAC)
  \\ IMP_RES_TAC (METIS_PROVE [] ``(xs = ys) ==> (mw2n xs = mw2n ys)``)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_n2mw,GSYM AND_IMP_INTRO,
       LENGTH_n2mw_LESS_LENGTH_n2mw] (Q.SPECL [`n2mw n`,`n2mw m`] mw_subv_thm))
  THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ `Num (ABS i) <= Num (ABS j)` by intLib.COOPER_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_n2mw,GSYM AND_IMP_INTRO,
       LENGTH_n2mw_LESS_LENGTH_n2mw] (Q.SPECL [`n2mw n`,`n2mw m`] mw_subv_thm))
  \\ intLib.COOPER_TAC);

val mwi_sub_lemma = prove(
  ``!s t xs ys.
      mw_ok xs /\ mw_ok ys ==>
      (mw2i (mwi_sub (s,xs) (t,ys)) = mw2i (s,xs) - mw2i (t,ys))``,
  ASM_SIMP_TAC std_ss [mwi_add_lemma,mwi_sub_def] \\ Cases_on `t`
  \\ ASM_SIMP_TAC std_ss [mw2i_def,INT_ADD_REDUCE,INT_ADD_CALCULATE,
      INT_SUB_REDUCE,INT_SUB_CALCULATE]);

val mwi_sub_lemma2 = RW [mw_ok_n2mw,GSYM i2mw_def,mw2i_i2mw]
  (Q.SPECL [`i<0:int`,`j<0:int`,`n2mw (Num (ABS i))`,`n2mw (Num (ABS j))`]
    mwi_sub_lemma);

val mwi_sub_thm = Q.store_thm("mwi_sub_thm",
  `!i j. mwi_sub (i2mw i) (i2mw j) = i2mw (i - j)`,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC mw2i_EQ_IMP_EQ_i2mw
  \\ FULL_SIMP_TAC std_ss [mwi_sub_lemma2]
  \\ SIMP_TAC std_ss [mwi_sub_def,mwi_add_def,i2mw_def,mw2n_n2mw] \\ STRIP_TAC
  THEN1 SRW_TAC [] [mw_ok_addv,mw_ok_n2mw,mw_subv_def,mw_ok_mw_fix,mw_ok_CLAUSES]
  \\ SRW_TAC [] [] \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_addv_IMP_NIL \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  THEN1 (FULL_SIMP_TAC std_ss [mw_addv_def,n2mw_NIL] \\ intLib.COOPER_TAC)
  \\ IMP_RES_TAC (METIS_PROVE [] ``(xs = ys) ==> (mw2n xs = mw2n ys)``)
  \\ FULL_SIMP_TAC std_ss [mw2n_def]
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_n2mw,GSYM AND_IMP_INTRO,
       LENGTH_n2mw_LESS_LENGTH_n2mw] (Q.SPECL [`n2mw n`,`n2mw m`] mw_subv_thm))
  \\ FULL_SIMP_TAC std_ss [] THEN1 DECIDE_TAC
  \\ `Num (ABS i) <= Num (ABS j)` by intLib.COOPER_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [mw2n_n2mw,GSYM AND_IMP_INTRO,
       LENGTH_n2mw_LESS_LENGTH_n2mw] (Q.SPECL [`n2mw n`,`n2mw m`] mw_subv_thm))
  \\ DECIDE_TAC);


(* mul *)

val single_mul_def = Define `
  single_mul (x:'a word) (y:'a word) (c:'a word) =
    (x * y + c, n2w ((w2n x * w2n y + w2n c) DIV dimword (:'a)):'a word)`;

val single_mul_add_def = Define `
  single_mul_add p q k s =
    let (x,kc) = single_mul p q k in
    let (zs,c) = mw_add [x;kc] [s;0w] F in
      (HD zs, HD (TL zs))`;

val mw_mul_pass_def = Define `
  (mw_mul_pass x [] zs k = [k]) /\
  (mw_mul_pass x (y::ys) zs k =
    let (y1,k1) = single_mul_add x y k (HD zs) in
      y1 :: mw_mul_pass x ys (TL zs) k1)`;

val mw_mul_def = Define `
  (mw_mul [] ys zs = zs) /\
  (mw_mul (x::xs) ys zs =
    let zs2 = mw_mul_pass x ys zs 0w in
      HD zs2 :: mw_mul xs ys (TL zs2))`;

val mwi_mul_def = Define `
  mwi_mul (s,xs) (t,ys) =
    if (xs = []) \/ (ys = []) then (F,[]) else
      (~(s = t), mw_fix (mw_mul xs ys (MAP (\x.0w) ys)))`;

val single_mul_thm = prove(
  ``!(x:'a word) y k z l.
      (single_mul x y k = (z,l)) ==>
      (w2n z + dimword (:'a) * w2n l = w2n x * w2n y + w2n k)``,
  NTAC 3 Cases_word \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [single_mul_def,w2n_n2w,LESS_MOD,b2w_def]
  \\ `(n * n' + n'') DIV dimword (:'a) < dimword (:'a)` by
      (SIMP_TAC std_ss [DIV_LT_X,ZERO_LT_dimword]
       \\ MATCH_MP_TAC MULT_ADD_LESS_MULT \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [word_add_n2w,word_mul_n2w,w2n_n2w]
  \\ METIS_TAC [DIVISION,MULT_COMM,ADD_COMM,ZERO_LT_dimword]);

val ADD_LESS_MULT = Q.prove(
  `!n. 1 < n ==> n + (n - 1) < n * n`,
  Induct \\ SIMP_TAC std_ss [MULT_CLAUSES] \\ REPEAT STRIP_TAC
  \\ Cases_on `1<n` \\ RES_TAC THEN1 DECIDE_TAC
  \\ `n = 1` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []);

val single_mul_add_thm = prove(
  ``!(p:'a word) q k1 k2 x1 x2.
      (single_mul_add p q k1 k2 = (x1,x2)) ==>
      (w2n x1 + dimword (:'a) * w2n x2 = w2n p * w2n q + w2n k1 + w2n k2)``,
  SIMP_TAC std_ss [single_mul_add_def] \\ BasicProvers.LET_ELIM_TAC
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_add_thm \\ FULL_SIMP_TAC bool_ss [LENGTH,dimwords_thm]
  \\ FULL_SIMP_TAC std_ss [mw2n_def,w2n_n2w,ZERO_LT_dimword,b2n_def]
  \\ `?z1 z2. zs = [z1;z2]` by
   (Q.PAT_X_ASSUM `mw_add _ _ _ = _` MP_TAC \\ FULL_SIMP_TAC std_ss [mw_add_def]
    \\ BasicProvers.LET_ELIM_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [HD,TL,mw2n_def]
  \\ IMP_RES_TAC single_mul_thm \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss [b2n_def] \\ CCONTR_TAC
  \\ `dimword (:'a) * dimword (:'a) <= w2n p * w2n q + w2n k1 + w2n k2` by DECIDE_TAC
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ `w2n p < dimword (:'a) /\ w2n k1 < dimword (:'a)` by METIS_TAC [w2n_lt]
  \\ `w2n q < dimword (:'a) /\ w2n k2 < dimword (:'a)` by METIS_TAC [w2n_lt]
  \\ `w2n p <= dimword (:'a) - 1` by DECIDE_TAC
  \\ `w2n q <= dimword (:'a) - 1` by DECIDE_TAC
  \\ `w2n p * w2n q <= (dimword (:'a) - 1) * (dimword (:'a) - 1)` by METIS_TAC [LESS_MONO_MULT2]
  \\ FULL_SIMP_TAC std_ss [LEFT_SUB_DISTRIB,RIGHT_SUB_DISTRIB,GSYM SUB_PLUS]
  \\ ASSUME_TAC (MATCH_MP ADD_LESS_MULT ONE_LT_dimword)
  \\ Q.ABBREV_TAC `d = dimword(:'a)` \\ DECIDE_TAC);

val mw_mul_pass_thm = Q.prove(
  `!ys zs (x:'a word) k.
      (LENGTH ys = LENGTH zs) ==>
      (mw2n (mw_mul_pass x ys zs k) = w2n x * mw2n ys + mw2n zs + w2n k) /\
      (LENGTH (mw_mul_pass x ys zs k) = LENGTH ys + 1)`,
  Induct \\ Cases_on `zs` \\ SIMP_TAC std_ss
    [mw_mul_pass_def,LENGTH,dimwords_thm,mw2n_def,DECIDE ``~(SUC n = 0)``,HD,TL]
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t`) \\ REPEAT STRIP_TAC
  \\ BasicProvers.LET_ELIM_TAC
  \\ FULL_SIMP_TAC std_ss [mw2n_def,LEFT_ADD_DISTRIB,LENGTH,ADD1,TL]
  \\ IMP_RES_TAC single_mul_add_thm \\ DECIDE_TAC);

val mw_mul_thm = Q.store_thm("mw_mul_thm",
  `!xs ys (zs:'a word list).
      (LENGTH ys = LENGTH zs) ==>
      (mw2n (mw_mul xs ys zs) = mw2n xs * mw2n ys + mw2n zs)`,
  Induct \\ SIMP_TAC std_ss [mw_mul_def,mw2n_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [LET_DEF,mw2n_def]
  \\ (STRIP_ASSUME_TAC o UNDISCH o Q.SPECL [`ys`,`zs`,`h`,`0w`]) mw_mul_pass_thm
  \\ Q.ABBREV_TAC `qs = mw_mul_pass h ys zs (0w:'a word)` \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `qs` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(0 = SUC n)``,ADD1]
  \\ FULL_SIMP_TAC std_ss [TL,HD,mw2n_def,w2n_n2w,ZERO_LT_dimword]
  \\ DECIDE_TAC);

val Num_ABS_EQ_0 = Q.prove(
  `!i. (Num (ABS i) = 0) = (i = 0)`,
  intLib.COOPER_TAC);

val NUM_EXISTS = Q.prove(
  `!i. ?n. ABS i = & n`,
  REPEAT STRIP_TAC \\ Cases_on `i < 0:int` \\ ASM_SIMP_TAC std_ss [INT_ABS]
  THEN1 (Q.EXISTS_TAC `Num (-i)` \\ intLib.COOPER_TAC)
  THEN1 (Q.EXISTS_TAC `Num i` \\ intLib.COOPER_TAC));

val mwi_mul_thm = Q.store_thm("mwi_mul_thm",
  `!i j. mwi_mul (i2mw i) (i2mw j) = i2mw (i * j)`,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [i2mw_def,mwi_mul_def,n2mw_NIL,Num_ABS_EQ_0]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Cases_on `i = 0`
  THEN1 ASM_SIMP_TAC std_ss [n2mw_NIL,Num_ABS_EQ_0,INT_MUL_REDUCE,INT_LT_REFL]
  \\ Cases_on `j = 0`
  THEN1 ASM_SIMP_TAC std_ss [n2mw_NIL,Num_ABS_EQ_0,INT_MUL_REDUCE,INT_LT_REFL]
  \\ `i * j < 0 = ~(i < 0 = j < 0)` by
        (SIMP_TAC std_ss [INT_MUL_SIGN_CASES] \\ intLib.COOPER_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ MATCH_MP_TAC IMP_EQ_n2mw \\ ASM_SIMP_TAC std_ss [mw_ok_mw_fix]
  \\ ASM_SIMP_TAC std_ss [mw2n_mw_fix,LENGTH_MAP,mw_mul_thm,mw2n_n2mw,
       RW [APPEND,mw2n_def] (Q.SPEC `[]` mw2n_MAP_ZERO),GSYM INT_ABS_MUL]
  \\ STRIP_ASSUME_TAC (Q.SPEC `i` NUM_EXISTS)
  \\ STRIP_ASSUME_TAC (Q.SPEC `j` NUM_EXISTS)
  \\ ASM_SIMP_TAC std_ss [INT_MUL,NUM_OF_INT,AC MULT_COMM MULT_ASSOC]);


(* div by 2 *)

val mw_shift_def = Define `
  (mw_shift [] = []) /\
  (mw_shift [w] = [w >>> 1]) /\
  (mw_shift ((w:'a word)::x::xs) =
     (w >>> 1 !! x << (dimindex (:'a) - 1)) :: mw_shift (x::xs))`;

val w2n_add = Q.prove(
  `!x y. w2n (x + y) = (w2n x + w2n (y:'a word)) MOD dimword (:'a)`,
  REPEAT Cases \\ SIMP_TAC std_ss [word_add_n2w,w2n_n2w,MOD_PLUS,ZERO_LT_dimword]);

val word_LSL_n2w = Q.prove(
  `!m k. ((n2w m):'a word) << k = n2w (m * 2 ** k)`,
  SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,WORD_MUL_LSL,word_mul_n2w]);

val mw_shift_thm = Q.store_thm("mw_shift_thm",
  `!xs. mw2n (mw_shift xs) = mw2n (xs:'a word list) DIV 2`,
  Induct \\ SIMP_TAC std_ss [mw_shift_def,mw2n_def]
  \\ Cases_on `xs` \\ ASM_SIMP_TAC std_ss [mw_shift_def,mw2n_def,w2n_lsr]
  \\ CONV_TAC (RAND_CONV (ALPHA_CONV ``w:'a word``)) \\ REPEAT STRIP_TAC
  \\ `w >>> 1 && h << (dimindex (:'a) - 1) = 0w` by ALL_TAC THEN1
   (SIMP_TAC std_ss [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,
      word_lsr_def,word_lsl_def,word_0]
    \\ REPEAT STRIP_TAC \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC WORD_ADD_OR \\ POP_ASSUM (fn th => SIMP_TAC std_ss [GSYM th])
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`h`,`h`) \\ Q.SPEC_TAC (`w`,`w`) \\ Cases \\ Cases
  \\ ASM_SIMP_TAC std_ss [w2n_add,w2n_lsr,word_LSL_n2w,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [dimword_def]
  \\ `0 < dimindex (:'a)` by METIS_TAC [DIMINDEX_GT_0]
  \\ `dimindex (:'a) = (dimindex (:'a) - 1) + 1` by DECIDE_TAC
  \\ Q.ABBREV_TAC `d = dimindex (:'a) - 1`
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,EXP]
  \\ SIMP_TAC std_ss [RW1 [MULT_COMM] (GSYM MOD_COMMON_FACTOR)]
  \\ `n DIV 2 + n' MOD 2 * 2 ** d < 2 * 2 ** d` by ALL_TAC THEN1
    (ONCE_REWRITE_TAC [ADD_COMM] \\ MATCH_MP_TAC MULT_ADD_LESS_MULT
     \\ FULL_SIMP_TAC std_ss [DIV_LT_X,AC MULT_COMM MULT_ASSOC])
  \\ ASM_SIMP_TAC std_ss [GSYM MULT_ASSOC]
  \\ ASM_SIMP_TAC std_ss [RW1 [ADD_COMM] (RW1 [MULT_COMM] ADD_DIV_ADD_DIV)]
  \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC,ADD_ASSOC]
  \\ `n' = n' DIV 2 * 2 + n' MOD 2` by METIS_TAC [DIVISION,DECIDE ``0<2``]
  \\ POP_ASSUM (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC,ADD_ASSOC]
  \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC]);

val LENGTH_mw_shift = Q.store_thm("LENGTH_mw_shift",
  `!xs. LENGTH (mw_shift xs) = LENGTH xs`,
  Induct \\ SIMP_TAC std_ss [LENGTH,mw_shift_def]
  \\ Cases_on `xs` \\ ASM_SIMP_TAC std_ss [LENGTH,mw_shift_def]);


(* compare *)

val mw_cmp_def = tDefine "mw_cmp" `
  mw_cmp xs ys = if xs = [] then NONE else
                 if LAST xs = LAST ys then
                   mw_cmp (BUTLAST xs) (BUTLAST ys)
                 else SOME (LAST xs <+ LAST ys)`
  (WF_REL_TAC `measure (LENGTH o FST)` \\ Cases \\ Cases
   \\ SIMP_TAC std_ss [LENGTH_BUTLAST,NOT_NIL_CONS,LENGTH])

val mw_compare_def = Define `
  mw_compare xs ys =
    if LENGTH xs < LENGTH ys then SOME (0 < 1) else
    if LENGTH ys < LENGTH xs then SOME (1 < 0) else mw_cmp xs ys`;

val option_eq_def = Define `
  (option_eq b NONE = NONE) /\
  (option_eq b (SOME x) = SOME (~(b = x)))`;

val mwi_compare_def = Define `
  mwi_compare (s,xs) (t,ys) =
    if s = t then option_eq s (mw_compare xs ys) else SOME s`;

val mwi_lt_def = Define `
  mwi_lt s_xs t_ys = (mwi_compare s_xs t_ys = SOME T)`;

val mwi_eq_def = Define `
  mwi_eq s_xs t_ys = (mwi_compare s_xs t_ys = NONE)`;

val LAST_IMP_mw2n_LESS_mw2n = Q.prove(
  `!xs ys. (LENGTH xs = LENGTH ys) /\ (LAST xs <+ LAST ys) /\ ~(xs = []) ==>
            mw2n xs < mw2n ys`,
  STRIP_TAC \\ `(xs = []) \/ ?x xs1. xs = SNOC x xs1` by METIS_TAC [SNOC_CASES]
  \\ STRIP_TAC \\ `(ys = []) \/ ?y ys1. ys = SNOC y ys1` by METIS_TAC [SNOC_CASES]
  \\ ASM_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH,DECIDE ``~(SUC n = 0)``,LAST_SNOC]
  \\ SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ MATCH_MP_TAC MULT_ADD_LESS_MULT_ADD
  \\ FULL_SIMP_TAC std_ss [mw2n_lt,WORD_LO] \\ METIS_TAC [mw2n_lt]);

val mw_cmp_thm = Q.store_thm("mw_cmp_thm",
  `!xs ys. (LENGTH ys = LENGTH xs) ==>
            (mw_cmp xs ys = if mw2n xs = mw2n ys then NONE else
                              SOME (mw2n xs < mw2n ys))`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_cmp_def]
  THEN1 FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
  \\ `(ys = []) \/ ?z zs. ys = SNOC z zs` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(0 = SUC n)``,LENGTH_SNOC]
  \\ FULL_SIMP_TAC std_ss [LAST_SNOC,NOT_NIL_SNOC]
  \\ Cases_on `x = z` \\ ASM_SIMP_TAC std_ss [FRONT_SNOC]
  THEN1 ASM_SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND]
  \\ Cases_on `x <+ z` \\ ASM_SIMP_TAC std_ss [] THEN1
   (REV (`mw2n (SNOC x xs) < mw2n (SNOC z zs)` by ALL_TAC) THEN1 DECIDE_TAC
    \\ METIS_TAC [LAST_IMP_mw2n_LESS_mw2n,LENGTH_SNOC,LAST_SNOC,NOT_NIL_SNOC])
  \\ MATCH_MP_TAC (DECIDE ``n < m ==> m <> n /\ ~(m < n:num)``)
  \\ METIS_TAC [LAST_IMP_mw2n_LESS_mw2n,LENGTH_SNOC,LAST_SNOC,NOT_NIL_SNOC,
                 WORD_LOWER_LOWER_CASES]);

val LENGTH_LESS_IMP_mw2n_LESS = Q.store_thm("LENGTH_LESS_IMP_mw2n_LESS",
  `!(xs:'a word list) (ys:'a word list).
      mw_ok xs /\ mw_ok ys /\ LENGTH xs < LENGTH ys ==> mw2n xs < mw2n ys`,
  REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.ISPEC `ys:'a word list` SNOC_CASES)
  \\ FULL_SIMP_TAC std_ss [LENGTH,mw_ok_def,NOT_SNOC_NIL,LAST_SNOC,LENGTH_SNOC]
  \\ SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def]
  \\ Q.PAT_X_ASSUM `~(x = 0w)` MP_TAC \\ Q.SPEC_TAC (`x`,`x`)
  \\ Cases \\ ASM_SIMP_TAC std_ss [n2w_11,w2n_n2w,ZERO_LT_dimword]
  \\ REPEAT STRIP_TAC \\ ASSUME_TAC (Q.ISPEC `xs:'a word list` mw2n_lt)
  \\ `dimwords (LENGTH xs) (:'a) <= dimwords (LENGTH l) (:'a)` by
       (SIMP_TAC std_ss [dimwords_def] \\ DECIDE_TAC)
  \\ `0 < dimwords (LENGTH l) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
  \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES] \\ DECIDE_TAC);

val mw2n_LESS_IMP_LENGTH_LESS_EQ = Q.store_thm("mw2n_LESS_IMP_LENGTH_LESS_EQ",
  `!xs:'a word list ys:'a word list.
      mw_ok xs /\ mw_ok ys /\ mw2n xs < mw2n ys ==> LENGTH xs <= LENGTH ys`,
  SIMP_TAC std_ss [GSYM NOT_LESS] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC LENGTH_LESS_IMP_mw2n_LESS \\ DECIDE_TAC);

val mw_compare_thm = Q.store_thm("mw_compare_thm",
  `!xs ys. mw_ok xs /\ mw_ok ys ==>
            (mw_compare xs ys = if mw2n xs = mw2n ys then NONE else
                                  SOME (mw2n xs < mw2n ys))`,
  REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [mw_compare_def]
  \\ Cases_on `LENGTH xs = LENGTH ys` \\ ASM_SIMP_TAC std_ss [mw_cmp_thm]
  \\ `LENGTH xs < LENGTH ys \/ LENGTH ys < LENGTH xs` by DECIDE_TAC
  \\ IMP_RES_TAC LENGTH_LESS_IMP_mw2n_LESS
  \\ IMP_RES_TAC (DECIDE ``m < n ==> ~(n < m) /\ ~(m = n:num)``)
  \\ ASM_SIMP_TAC std_ss []);

val mwi_compare_thm = Q.store_thm("mwi_compare_thm",
  `!i j. mwi_compare (i2mw i) (i2mw j) = if i = j then NONE else SOME (i < j)`,
  SIMP_TAC std_ss [i2mw_def,mwi_compare_def,mw_compare_thm,mw_ok_n2mw,mw2n_n2mw]
  \\ REPEAT STRIP_TAC \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss [option_eq_def]
  \\ REV (Cases_on `i < 0 = j < 0`) \\ ASM_SIMP_TAC std_ss [] THEN1 intLib.COOPER_TAC
  \\ Cases_on `i < 0` \\ Cases_on `j < 0` \\ SRW_TAC [] [option_eq_def,INT_ABS]
  \\ intLib.COOPER_TAC);

val mw_subv_NOT_NIL = Q.store_thm("mw_subv_NOT_NIL",
  `!xs ys. mw_ok xs /\ mw_ok ys /\ mw2n xs < mw2n ys ==> ~(mw_subv ys xs = [])`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC mw2n_LESS_IMP_LENGTH_LESS_EQ
  \\ `mw2n xs <= mw2n ys` by DECIDE_TAC \\ IMP_RES_TAC mw_subv_thm
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [mw2n_def] \\ DECIDE_TAC);


(* alternative compare *)

val mw_cmp_alt_def = Define `
  (mw_cmp_alt [] ys b = b) /\
  (mw_cmp_alt (x::xs) ys b =
     mw_cmp_alt xs (TL ys) (if x = HD ys then b else
                            if x <+ HD ys then SOME T else SOME F))`

val mw_cmp_CONS = Q.prove(
  `!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (mw_cmp (x::xs) (y::ys) =
        case mw_cmp xs ys of NONE => mw_cmp [x] [y] | t => t)`,
  HO_MATCH_MP_TAC (fetch "-" "mw_cmp_ind") \\ REPEAT STRIP_TAC
  \\ `(xs = []) \/ ?x1 l1. xs = SNOC x1 l1` by METIS_TAC [SNOC_CASES]
  \\ `(ys = []) \/ ?x2 l2. ys = SNOC x2 l2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``mw_cmp [] []``]
  \\ SIMP_TAC (srw_ss()) [Once mw_cmp_def,LAST_DEF,FRONT_DEF]
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC (srw_ss()) [Once mw_cmp_def,LAST_SNOC,FRONT_SNOC]
  \\ Cases_on `x1 = x2` \\ FULL_SIMP_TAC std_ss []);

val mw_cmp_alt_lemma = Q.prove(
  `!xs ys res.
      (LENGTH xs = LENGTH ys) ==>
      (mw_cmp_alt xs ys res =
         case mw_cmp xs ys of NONE => res | SOME t => SOME t)`,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [mw_cmp_alt_def,HD,TL]
  THEN1 (STRIP_TAC \\ EVAL_TAC)
  \\ REPEAT STRIP_TAC \\ Cases_on `h = h'` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!xx.bb` (MP_TAC o Q.SPEC `t`)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [Once mw_cmp_CONS]
  \\ Cases_on `mw_cmp xs t` \\ FULL_SIMP_TAC std_ss []
  \\ EVAL_TAC \\ Cases_on `h = h'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] []);

val mw_cmp_alt_thm = Q.store_thm("mw_cmp_alt_thm",
  `(LENGTH xs = LENGTH ys) ==>
    (mw_cmp xs ys = mw_cmp_alt xs ys NONE)`,
  Cases_on `mw_cmp xs ys` \\ ASM_SIMP_TAC std_ss [mw_cmp_alt_lemma]);


(* Division *)

(* Following will be a definition of a division algorithm miming that
   described by Donald E. Knuth in "The Art of Computer
   Programming". (Found in "Volume II: Seminumerical Algorithms", on
   pages 270-273 in the most recent edition (3rd edition, 1997)).

   It is meant to compute the quotient of a word list x_{1}...x_{m+n}
   by a word list y_{1}...y{n} where n and m are natural numbers, and
   the words have arbitrary dimension b = 2 ^ k, for some given
   natural k.

   For this section, the digits of the word-list inputs are ordered in
   reverse - that is, with the most significant bit as head *)

(* General Definitions *)

val mw_mul_by_single_def = Define `
  mw_mul_by_single (x:'a word) (ys:'a word list) =
    mw_mul_pass x ys (k2mw (LENGTH ys) 0) 0w`;

val LENGTH_mw_mul_pass = Q.store_thm("LENGTH_mw_mul_pass",
  `!ys zs (x:'a word) k.
      (LENGTH (mw_mul_pass x ys zs k) = LENGTH ys + 1)`,
  Induct \\ Cases_on `zs`
  \\ FULL_SIMP_TAC (srw_ss()) [mw_mul_pass_def,single_mul_add_def,LET_DEF,
       single_mul_def,mw_add_def,single_add_def] \\ DECIDE_TAC);

val LENGTH_mw_mul_by_single = Q.store_thm("LENGTH_mw_mul_by_single",
  `(LENGTH (mw_mul_by_single x ys) = LENGTH ys + 1)`,
  SIMP_TAC std_ss [LENGTH_mw_mul_pass,mw_mul_by_single_def]);

val PULL_CONJ = METIS_PROVE [] ``!a b c.( a ==> b /\ c) ==>(a ==> b) /\ (a ==> c)``

(*   Two theorems and corresponding tactics for handling equations
     in a more "high-level" way, compared with the ones I know.          *)

val EQ_M_R_S_i =
  GEN_ALL (CONJUNCT2
   (MP (Q.SPECL [`m*n < p*n`,`0<n`,`m<p`] PULL_CONJ)
        ((fn (x,y) => x) (EQ_IMP_RULE (SPEC_ALL LT_MULT_RCANCEL)))))

val EQT_M_R_S_i = fn x => (MATCH_MP_TAC (Q.SPECL [`xxx`,x,`yyy`] EQ_M_R_S_i))

val EQ_A_S_R_2 = store_thm ("EQ_A_S_R_2",
  ``!c d a b. d <= c /\ a + c < b + d ==> a < b``,
  REPEAT strip_tac  >> RW_TAC arith_ss[]);

val EQT_A_S_R_2 =
  (* If the goal is `a < b` and `c <= d` is an assumption, transforms current goal into `a + c < b + d` *)
  fn (c,d) =>
    (MATCH_MP_TAC
    (Q.SPECL [c,d,`xxx`,`yyy`] EQ_A_S_R_2)
    >> strip_tac THEN1 METIS_TAC[]);

(* division arithmetic lemmas*)

val DIV_thm2 = Q.store_thm( "DIV_thm2",
  `0 < b /\ a < c * b ==> a DIV b < c`,
  strip_tac >> METIS_TAC[DIV_LT_X]);

val DIV_thm3 = Q.store_thm( "DIV_thm3",
  `!a b. 0 < b ==> (a DIV b * b <= a)`,
  REPEAT strip_tac >> IMP_RES_TAC DIVISION >> METIS_TAC[LESS_EQ_ADD]);

val DIV_thm4 = Q.store_thm( "DIV_thm4",
  `!a b. 0 < b ==> (a - a DIV b * b < b)`,
  REPEAT strip_tac >> IMP_RES_TAC DIVISION >>
  METIS_TAC[MOD_LESS_EQ,DIV_thm3,CANCEL_SUB,ADD_SUB,ADD_COMM]);

val DIV_thm4_bis = Q.store_thm( "DIV_thm4_bis",
  `!a b. 0 < b ==> a < b + a DIV b * b`, strip_tac >>
  METIS_TAC[DIV_EQ_X,MULT,ADD_COMM]);

val DIV_thm1 = Q.store_thm( "DIV_thm1",
  `0 < b /\ b <= c ==> a DIV c <= a DIV b` ,
  strip_tac >> qsuff_tac `a < (a DIV b + 1) * c` THEN1 (
  strip_tac >> METIS_TAC[LESS_LESS_EQ_TRANS,DIV_LE_X]) >>
  MATCH_MP_TAC LESS_LESS_EQ_TRANS >> EXISTS_TAC ``(a DIV b + 1)*b`` >> strip_tac THEN1
  METIS_TAC[DIV_thm4_bis,RIGHT_ADD_DISTRIB,MULT_LEFT_1,ADD_COMM] >>
  METIS_TAC[MULT_COMM,LESS_MONO_MULT]);

val DIV_thm5 = Q.store_thm( "DIV_thm5",
  `0 < b /\ a - q*b < b ==> (q >= a DIV b)`,
  rw[GREATER_EQ] >> rw[DIV_LE_X] >> srw_tac[ARITH_ss][]);

(* lists *)

val NOT_NIL_EQ_LENGTH_NOT_0 = store_thm ( "NOT_NIL_EQ_LENGTH_NOT_0",
  ``x <> [] <=> (0 < LENGTH x)``,
  Cases_on `x` >> lrw[]);

val HD_REVERSE = store_thm ("HD_REVERSE",
  ``!x. x <> [] ==> (HD (REVERSE x) = LAST x)``,
  REPEAT strip_tac >>
  Induct_on `x` THEN1 fs[] >>
  rw[LAST_DEF] >>
  Cases_on `REVERSE x` THEN1 fs[] >>
  fs[]);

(* word & multiWord general *)

val NOT_0w_bis = Q.store_thm("NOT_0w_bis",
  `w <> 0w ==> 0 < w2n w`,
  Cases_on `w`>> fs [] >> DECIDE_TAC);

val dimwords_dimword = Q.store_thm("dimwords_dimword",
  `!n. dimwords n (:'a) = dimword(:'a) ** n`,
  rw[dimwords_def,dimword_def,Once MULT_COMM] >>
  Induct_on `n` THEN1 rw[] >>
  METIS_TAC[MULT_COMM,MULT,EXP,EXP_ADD]);

val mw2n_msf = store_thm ("mw2n_msf" ,
  ``!(x:'a word) xs. mw2n (xs++[x]) = mw2n xs + dimwords (LENGTH xs) (:'a) * w2n x``,
  Induct_on `xs` >>
  lrw[mw2n_def, EXP,dimwords_def,dimword_def,LEFT_ADD_DISTRIB] >>
  REWRITE_TAC[MULT,DECIDE ``z * dimindex (:'a) = dimindex (:'a) * z``] >>
  METIS_TAC[MULT_ASSOC,EXP_ADD,ADD_COMM]);

val mw2n_msf_NIL = store_thm ("mw2n_msf_NIL",
  ``!(xs:'a word list). (xs <> []) /\
                        (mw2n xs < dimwords (LENGTH (FRONT xs)) (:'a)) ==>
                        (mw2n xs = mw2n (FRONT xs))``,
  REPEAT strip_tac >>
  `mw2n xs = mw2n (FRONT xs ++ [LAST xs])` by METIS_TAC[APPEND_FRONT_LAST] >>
  POP_ASSUM (fn x => FULL_SIMP_TAC std_ss [x,mw2n_msf]) >>
  METIS_TAC[LESS_EQ_ADD,ADD_COMM,LESS_EQ_LESS_TRANS,LT_MULT_CANCEL_RBARE]);

val mw2n_k2mw_0 = Q.store_thm( "mw2n_k2mw_0",
  `!x. mw2n ((k2mw x 0):'a word list) = 0`,
  Induct_on `x` THEN1 METIS_TAC[k2mw_def,mw2n_def] >>
  `0 DIV dimword(:'a) = 0` by METIS_TAC[ZERO_LT_dimword,ZERO_DIV] >>
  RW_TAC std_ss [word_0_n2w,k2mw_def,mw2n_def]);

val mw_mul_by_single_lemma = Q.store_thm( "mw_mul_by_single_lemma",
  `!(x:'a word) (ys:'a word list).
    (mw2n (mw_mul_by_single x ys) = w2n x * mw2n ys) /\
    (LENGTH (mw_mul_by_single x ys) = LENGTH ys + 1)`,
  REPEAT strip_tac >>
  REWRITE_TAC[mw_mul_by_single_def] >>
  `LENGTH (ys:'a word list) = LENGTH ((k2mw (LENGTH ys) 0): 'a word list)`
  by METIS_TAC[LENGTH_k2mw] >>
  IMP_RES_TAC (SPEC_ALL mw_mul_pass_thm) >> lrw[mw2n_k2mw_0]);

val word_reverse_lsl = Q.prove(
  `!w n. word_reverse (w << n) = (word_reverse w >>> n):'a word`,
  FULL_SIMP_TAC std_ss [word_reverse_def,word_lsl_def,word_lsr_def,
    fcpTheory.CART_EQ,fcpTheory.FCP_BETA] \\ REPEAT STRIP_TAC
  \\ `(dimindex (:'a) - 1 - i) < dimindex (:'a)` by DECIDE_TAC
  \\ Cases_on `i + n < dimindex (:'a)`
  \\ FULL_SIMP_TAC std_ss [fcpTheory.FCP_BETA]
  \\ `i + n < dimindex (:'a) = n <= dimindex (:'a) - 1 - i` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [fcpTheory.FCP_BETA,SUB_PLUS]);

val word_reverse_EQ_ZERO = Q.prove(
  `!w:'a word. (word_reverse w = 0w) = (w = 0w)`,
  FULL_SIMP_TAC std_ss
   [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_reverse_def,word_0]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ `dimindex (:'a) - 1 - i < dimindex (:'a)` by DECIDE_TAC \\ RES_TAC
  \\ `dimindex (:'a) - 1 - (dimindex (:'a) - 1 - i) = i` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []);

val calc_d_def = tDefine "calc_d" `

(* Following is an algorithm that computes the normalisation factor
   (named d in Knuth's discussion) by which both xs and ys are multiplied
   to ensure that the most significant figure of ys in greater or equal to
   b / 2

   Since we are working with word-size b = 2 ^ k for some natural k,
   we produce the factor by multiplying the mentioned figure by 2
   successively until b / 2 is reached.  *)

  calc_d (v1:'a word, d:'a word) =
    if (v1 = 0w) \/ word_msb(v1) then d else
      calc_d (v1 * 2w, d * 2w)`
  (WF_REL_TAC `measure (\(v1,d). w2n (word_reverse v1))`
   \\ SIMP_TAC std_ss [WORD_MUL_LSL |> Q.SPECL [`w`,`1`] |>
          SIMP_RULE std_ss [Once WORD_MULT_COMM] |> GSYM]
   \\ FULL_SIMP_TAC std_ss [word_reverse_lsl,w2n_lsr]
   \\ REPEAT STRIP_TAC
   \\ `~(word_reverse v1 = 0w)` by FULL_SIMP_TAC std_ss [word_reverse_EQ_ZERO]
   \\ Cases_on `word_reverse v1`
   \\ FULL_SIMP_TAC (srw_ss()) [DIV_LT_X] \\ DECIDE_TAC);

val calc_d_ind = fetch "-" "calc_d_ind"

(* Definition *)

val single_div_def = Define `
  (single_div (x1:'a word) (x2:'a word) (y:'a word) =
  (n2w ((w2n x1 * dimword (:'a) + w2n x2) DIV w2n y): 'a word,
   n2w ((w2n x1 * dimword (:'a) + w2n x2) MOD w2n y): 'a word))`;

val mw_div_by_single_def = tDefine "mw_div_by_single" `

(* This algorithm forms the quotient of a multi-word number
   x_{1}x_{2}x_{3}...x_{n} by a single word y using the classic
   Euclidean division algorithm *)

  (mw_div_by_single [] (y:'a word) = [0w]:'a word list) /\
  (mw_div_by_single ([x]:'a word list) (y:'a word) = (\(a,b).if w2n x < w2n y then [b] else a::[b]) (single_div 0w x y)) /\
  (mw_div_by_single (x1::x2::xs:'a word list) (y:'a word) =
    if (w2n x1 < w2n y) \/ (w2n y = 0)
      then let (q,r) = single_div x1 x2 y in
      q::(mw_div_by_single (r::xs) y)
      else let (q,r) = single_div 0w x1 y in
      q::(mw_div_by_single (r::x2::xs) y))`

  (WF_REL_TAC`measure(\(xs,y). if w2n (HD xs) < w2n y
                             then 2 * LENGTH xs
                             else 2 * LENGTH xs + 1)` >>
   lrw[single_div_def] >>
   Cases_on `y = 0w` THEN1 METIS_TAC[] >>
   `0 < w2n y` by METIS_TAC[w2n_eq_0,NOT_ZERO_LT_ZERO] >>
   METIS_TAC[MOD_LESS,MOD_LESS_EQ,ZERO_LT_dimword,LESS_EQ_LESS_TRANS])

val mw_div_by_single_ind = fetch "-" "mw_div_by_single_ind"

val mw_simple_div_def = Define `
  (mw_simple_div x [] y = ([],x,T)) /\
  (mw_simple_div x (x1::xs) y =
     let c1 = x <+ y in
     let (q,r) = single_div x x1 y in
     let (qs,r,c) = mw_simple_div r xs y in
       (q::qs,r,c /\ c1))`;

val mw_div_test_def = tDefine "mw_div_test" `

(* This function encloses the 3rd step "D3" of Knuth's algorithm.  It
   is meant to take input q = u_{1}u_{2} / v_{1}, and either outputs Q
   or Q + 1, where Q = U / V, U = u_{1}u_{2}u_{3}...u_{n+1},
   V = v_{1}v_{2}...v_{n} are word lists with word-size b for some
   n > 1, and Q < b.

   Both if statements rephrase Knuth's tests, replacing the value of
   the remainder r of the division u1u2 / v1 by r = u1u2 - u1u2 / v1,
   and adding values on both sides of each equation to avoid
   substractions.  *)

  mw_div_test (q:'a word) (u1:'a word) (u2:'a word) (u3:'a word) (v1:'a word) (v2:'a word)  =
    if (mw_cmp [u3;u2;u1] (mw_mul_by_single q [v2;v1])) = SOME T
    then let q2 = n2w (w2n q - 1) in
         let s = single_mul q2 v1 0w in
          if (mw_cmp [u2;u1] (FST (mw_add [FST s; SND s] [0w;1w] F))) = SOME T
          then mw_div_test q2 u1 u2 u3 v1 v2
          else q2
    else q`

  (WF_REL_TAC `measure (\(q,u1,u2,u3,v1,v2). w2n q)` >>
  REPEAT strip_tac >>
  Cases_on `w2n q` THEN1 (
  qsuff_tac `mw_cmp [u3; u2; u1] (mw_mul_by_single 0w [v2; v1]) <> SOME T` THEN1 fs[] >>
  Q.PAT_ABBREV_TAC `x = mw_mul_by_single 0w [v2;v1]` >>
  Q.PAT_ABBREV_TAC `u = [u3;u2;u1]` >>
  `LENGTH x = LENGTH u` by fs[mw_mul_by_single_lemma,Abbr`x`,Abbr`u`] >>
  `~(mw2n u < mw2n x)` by rw[mw_mul_by_single_lemma,Abbr`x`] >>
  fs[mw_cmp_thm]) >>
  rw[SUC_SUB1] >>
  `n < dimword(:'a)` by METIS_TAC[w2n_lt,DECIDE ``n < SUC n``,LESS_TRANS] >>
  rw[]);

val mw_div_test_ind = fetch "-" "mw_div_test_ind"

val mw_div_loop_def = tDefine "mw_div_loop"

(* This algorithm encloses the steps between the 3rd "D3" and the
   seventh "D7" which are repeated m + 1 times, where the initial
   inputs are dividend xs = x_{1}...x_{m+n} and divisor ys =
   y_{1}...y_{n}, and the normalised dividend is x_{1}...x_{m+n+1}. *)

(*     Inputs are:

       zs = x_{1}...{j+n+1}
       us = x_{j}...x_{j+n+1}   ( j = m, m-1,..., 0 )
       q = x1x2 / y1

       q is then modified through mw_div_test.

       if us < q * ys,   quotient digit is q - 1
                         and input X becomes X - (q-1) * ys
       else              quotient digit is q
                         and input X's becomes X's - q * ys     *)

 `mw_div_loop (zs:'a word list) (ys:'a word list) =

  if LENGTH ys < LENGTH zs
  then let (us:'a word list) = TAKE (SUC(LENGTH ys)) zs in
       let q = if w2n (HD us) < w2n (HD ys)
               then FST (single_div (HD us) (HD (TL us)) (HD ys))
               else (n2w (dimword(:'a) - 1):'a word) in
       let q2 = mw_div_test q (HD us) (HD (TL us)) (HD (TL (TL us))) (HD ys) (HD (TL ys)) in
       let q2ys = mw_mul_by_single q2 (REVERSE ys) in

       if mw_cmp (REVERSE us) q2ys = SOME T
       then let q3 = (n2w (w2n q2 - 1):'a word) in
            let q3ys = mw_mul_by_single q3 (REVERSE ys) in
            let zs2 = (REVERSE (FRONT (FST(mw_sub (REVERSE us) q3ys T)))) ++ DROP (SUC(LENGTH ys)) zs in
            q3::(mw_div_loop zs2 ys)
       else let zs2 = (REVERSE (FRONT (FST(mw_sub (REVERSE us) q2ys T)))) ++ DROP (SUC(LENGTH ys)) zs in
            q2::(mw_div_loop zs2 ys)
  else zs`

(WF_REL_TAC `measure (LENGTH o FST)` >>
 REPEAT strip_tac >>
 Q.PAT_ABBREV_TAC `us = (TAKE (SUC (LENGTH ys)) zs)` >>
 Q.PAT_ABBREV_TAC `q = (if w2n (HD us) < w2n (HD ys) then
                          FST (single_div (HD us) (HD (TL us)) (HD ys))
                        else
                          n2w (dimword (:'a) - 1))` >>
 Q.PAT_ABBREV_TAC `q2 =(mw_div_test q (HD us) (HD (TL us))
                       (HD (TL (TL us))) (HD ys) (HD (TL ys)))` >>
  `LENGTH us = SUC (LENGTH ys)` by METIS_TAC[LENGTH_TAKE,LESS_EQ] THENL [

 Q.PAT_ABBREV_TAC `q3:'a word = n2w (w2n q2 - 1)` >>
 Q.PAT_ABBREV_TAC `q3ys = (mw_mul_by_single q3 (REVERSE ys))` >>
 `LENGTH (REVERSE us) = LENGTH q3ys` by METIS_TAC[LENGTH_REVERSE,Abbr`q3ys`,mw_mul_by_single_lemma,ADD1] >>
 Q.PAT_ABBREV_TAC `ws = FST (mw_sub (REVERSE us) q3ys T)` ,

 Q.PAT_ABBREV_TAC `q2ys = (mw_mul_by_single q2 (REVERSE ys))` >>
 `LENGTH (REVERSE us) = LENGTH q2ys` by METIS_TAC[LENGTH_REVERSE,Abbr`q2ys`,mw_mul_by_single_lemma,ADD1] >>
 Q.PAT_ABBREV_TAC `ws = FST (mw_sub (REVERSE us) q2ys T)` ] >>

 `LENGTH ws = LENGTH (REVERSE us)` by METIS_TAC[PAIR,mw_sub_lemma,Abbr`ws`] >>
 lrw[] >>
 qsuff_tac `ws <> []` THEN1 METIS_TAC[rich_listTheory.LENGTH_BUTLAST,LENGTH_REVERSE,prim_recTheory.PRE,DECIDE ``n < SUC n``] THEN1
 METIS_TAC[NULL,rich_listTheory.LENGTH_NOT_NULL,DECIDE ``0 < SUC n``,LENGTH_REVERSE] THEN1
 METIS_TAC[rich_listTheory.LENGTH_BUTLAST,LENGTH_REVERSE,prim_recTheory.PRE,DECIDE ``n < SUC n``] >>
 METIS_TAC[NULL,rich_listTheory.LENGTH_NOT_NULL,DECIDE ``0 < SUC n``,LENGTH_REVERSE])

val mw_div_loop_ind = fetch "-" "mw_div_loop_ind"

(* calc_d Lemmas  *)

val d_word_msb = Q.store_thm( "d_word_msb",
`!(a:'a word). word_msb a <=> dimword(:'a) DIV 2 <= w2n a`,
  Cases \\ `0 < dimindex (:'a)` by FULL_SIMP_TAC std_ss [DIMINDEX_GT_0]
  \\ `(dimindex(:'a)) - 1 < (dimindex (:'a))` by DECIDE_TAC
  \\ `2 ** SUC (dimindex(:'a) - 1) = dimword (:'a)` by
         (FULL_SIMP_TAC std_ss [dimword_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_msb_def,word_index,bitTheory.BIT_def,
         bitTheory.BITS_THM2,DIV_LE_X,DIV_EQ_X,GSYM EXP]
  \\ FULL_SIMP_TAC std_ss [dimword_def] \\ Cases_on `dimindex (:'a)`
  \\ FULL_SIMP_TAC std_ss [EXP] \\ DECIDE_TAC);

val d_lemma1 = store_thm ("d_lemma1",
``!(v1:'a word) (d:'a word) (x:'a word).
   calc_d (FST(v1,d),SND(v1,d)*x) = calc_d(v1,d) * x``,
  HO_MATCH_MP_TAC calc_d_ind >> REPEAT strip_tac >>
  rw[Once calc_d_def] THEN1 rw[Once calc_d_def] THEN1 rw[Once calc_d_def] >>
  fs[FST,SND] >>
  `!(x1:'a word) (x2:'a word). x1 * x2 = x2 * x1` by rw[] >>
  METIS_TAC[calc_d_def]);

val d_lemma2 = store_thm ("d_lemma2",
``!(v1:'a word) (d:'a word).
  FST(v1,d) <> 0w ==>
  dimword(:'a) DIV 2 <= w2n ((calc_d (FST(v1,d),1w:'a word)) * (FST (v1,d)))``,

  HO_MATCH_MP_TAC calc_d_ind >> REPEAT strip_tac >>
  rw[Once calc_d_def] THEN1 METIS_TAC[d_word_msb] >>
  fs[FST] >>
  `w2n d < dimword(:'a) DIV 2` by METIS_TAC[d_word_msb,NOT_LESS_EQUAL] >>
  `0 < 2` by DECIDE_TAC >>
  `(2 * w2n d) < dimword(:'a)` by METIS_TAC[MULT_COMM,DIV_thm3,LESS_LESS_EQ_TRANS,LT_MULT_RCANCEL] >>
  Cases_on `dimword(:'a) = 2` THEN1 (`w2n d = 0` by DECIDE_TAC >> METIS_TAC[w2n_eq_0]) >>
  ASSUME_TAC ONE_LT_dimword >> `2 < dimword(:'a)` by DECIDE_TAC >>
  `2w * d <> 0w` by rw[word_mul_def] >>
  `2w = 1w * 2w` by rw[] >>
  `calc_d(2w *d, 2w) = calc_d(2w*d,1w) * 2w` by METIS_TAC[d_lemma1,FST,SND] >> POP_ASSUM (fn x => REWRITE_TAC[x]) >>
  RES_TAC >>rw[]);

val d_lemma2_bis = store_thm ( "d_lemma2_bis",
``!(v1:'a word) (d:'a word).
  FST(v1,d) <> 0w ==> calc_d (FST(v1,d),1w) <> 0w``,
  REPEAT strip_tac >> IMP_RES_TAC d_lemma2 >>
  `w2n (calc_d (FST (v1,d),1w)) = 0` by METIS_TAC[word_0_n2w] >>
  fs[FST,word_mul_def] >>
  METIS_TAC[TWO,LESS_EQ,ONE_LT_dimword,DECIDE``0<2``,prim_recTheory.LESS_NOT_EQ,DIV_GT0]);

val d_lemma3 = store_thm ("d_lemma3",
``!(v1:'a word) (d:'a word).
  w2n (calc_d (FST(v1,d),1w:'a word)) * w2n (FST (v1,d)) < dimword(:'a)``,

  HO_MATCH_MP_TAC calc_d_ind >> REPEAT strip_tac >>
  srw_tac[][Once calc_d_def,w2n_lt] >>
  ASSUME_TAC d_lemma1 >>
  RES_TAC >> full_simp_tac (srw_ss())[FST,SND] >>
  `2w = 1w*2w` by srw_tac[][] >>
  `calc_d (2w * d,2w) = 2w * (calc_d (2w * d,1w))` by METIS_TAC[] >> POP_ASSUM (fn x => REWRITE_TAC[x]) >>
  Q.PAT_ABBREV_TAC` X = calc_d (2w * d,1w)` >>
  full_simp_tac (srw_ss())[word_mul_def] >>
  Cases_on `dimword(:'a) = 2` THEN1 full_simp_tac (srw_ss())[] >>
  ASSUME_TAC ONE_LT_dimword >>
  `2 < dimword(:'a)` by DECIDE_TAC >>
  `2 MOD dimword(:'a) = 2` by METIS_TAC[LESS_MOD] >>
  POP_ASSUM (fn x => full_simp_tac (srw_ss())[x]) >>
  `w2n d < dimword(:'a) DIV 2` by METIS_TAC[d_word_msb,NOT_LESS_EQUAL] >>
  `0 < 2` by DECIDE_TAC >>
  `(2 * w2n d) < dimword(:'a)` by METIS_TAC[MULT_COMM,DIV_thm3,LESS_LESS_EQ_TRANS,LT_MULT_RCANCEL] >>
  `(2 * w2n d) MOD dimword(:'a) = (2 * w2n d)` by srw_tac[][LESS_MOD] >> POP_ASSUM (fn x => full_simp_tac (srw_ss())[x]) >>
  `(2 * w2n X) * w2n d < dimword(:'a)` by RW_TAC arith_ss[] >>
  METIS_TAC[MOD_LESS_EQ,ZERO_LT_dimword,LESS_EQ_LESS_TRANS,LESS_MONO_MULT]);

val d_lemma4 = store_thm ("d_lemma4",
``!(v1:'a word) (d:'a word).
  ?n. w2n (calc_d (FST(v1,d),1w)) = 2 ** n``,

  HO_MATCH_MP_TAC calc_d_ind >> REPEAT strip_tac >> srw_tac[][Once calc_d_def] >> RES_TAC >>
  full_simp_tac (srw_ss())[FST] >>
  `2w = 1w * 2w` by srw_tac[][] >>
  `calc_d (2w * d,2w) = calc_d (2w * d,1w) * 2w` by METIS_TAC[d_lemma1,FST,SND] >>
  POP_ASSUM (fn x => REWRITE_TAC[x]) >> srw_tac[][word_mul_def] >>
  REWRITE_TAC[dimword_def] >> ASSUME_TAC dimword_def >>  Q.PAT_ABBREV_TAC `m = dimindex(:'a)` >> markerLib.RM_ABBREV_TAC "m" >>
  Cases_on `m = 1` THEN1 (
  `w2n d < 1` by METIS_TAC[d_word_msb,NOT_LESS_EQUAL,EVAL ``2 ** 1 DIV 2``] >>
  `w2n d = 0` by DECIDE_TAC >>
  METIS_TAC[w2n_eq_0]) >>
  Cases_on `m` THEN1 METIS_TAC[EXP,ONE_LT_dimword,prim_recTheory.LESS_NOT_EQ] >>
  `2 < dimword(:'a)` by srw_tac[][] THEN1(
  Cases_on `n'` THEN1 DECIDE_TAC >>
  srw_tac[][EXP] >> METIS_TAC[LE_MULT_CANCEL_LBARE,ZERO_LT_EXP,DECIDE ``0 < 2 /\ 1 < 2``, LESS_LESS_EQ_TRANS] ) >>
  qpat_x_assum `dimword(:'a) = xxx` (fn x => REWRITE_TAC [GSYM x] \\ (ASSUME_TAC x)) >>
  srw_tac[][LESS_MOD,DECIDE ``2 ** n * 2 = 2 * 2 ** n``,GSYM EXP] >>
  `SUC n < SUC n'` by ASSUME_TAC (Q.SPECL [`(2w:'a word)*(d:'a word)`,`x`] d_lemma3) THEN1(
  qpat_x_assum `2 < xxx` (fn x => full_simp_tac (srw_ss())[FST] \\ ASSUME_TAC x) >>
  qsuff_tac `w2n (calc_d (2w * d, 1w)) < dimword(:'a) DIV 2` THEN1 (strip_tac >>
  `dimword(:'a) DIV 2 = 2 ** SUC n' DIV 2 ** 1` by srw_tac[][] >>
  `dimword(:'a) DIV 2 = 2 ** n'` by METIS_TAC[SUC_SUB1,EXP_SUB,DECIDE ``(0 < 2) /\ (1 <= SUC n')`` ] >>
  ` 2 ** n < 2 ** n'` by METIS_TAC[] >> full_simp_tac (srw_ss())[]) >>
  `w2n (2w * d) = 2 * w2n d` by srw_tac[][word_mul_def] THEN1 (
  `w2n d < dimword(:'a) DIV 2` by METIS_TAC[d_word_msb,NOT_LESS_EQUAL] >>
  `0 < 2` by DECIDE_TAC >>
  METIS_TAC[MULT_COMM,DIV_thm3,LESS_LESS_EQ_TRANS,LT_MULT_RCANCEL]) >>
  POP_ASSUM (fn x => full_simp_tac (srw_ss())[x,EXP]) >> POP_ASSUM (K ALL_TAC) >>
  POP_ASSUM (fn x => ASSUME_TAC (RW [DECIDE ``a*(b*c) = a*c*b``] x)) >>
  `0 < w2n d` by METIS_TAC[NOT_0w_bis] >>
  ONCE_REWRITE_TAC[MULT_COMM] >> srw_tac[][MULT_DIV] >>
  METIS_TAC[LE_MULT_CANCEL_LBARE,LESS_EQ_LESS_TRANS,MULT_COMM,EQ_M_R_S_i,EXP_BASE_LT_MONO,DECIDE ``1 < 2``]) >>
  IMP_RES_TAC TWOEXP_MONO >> srw_tac[][LESS_MOD]);

val d_lemma5 = store_thm ("d_lemma5",
``!(v1:'a word) (d:'a word).
  2 <= w2n (calc_d (FST(v1,d),1w:'a word)) ==>
  w2n (calc_d (FST(v1,d),1w:'a word)) * SUC (w2n (FST (v1,d))) <= dimword(:'a)``,

  REPEAT strip_tac >>
  REWRITE_TAC[dimword_def] >> ASSUME_TAC dimword_def >>  Q.PAT_ABBREV_TAC `m = dimindex(:'a)` >> markerLib.RM_ABBREV_TAC "m" >>
  ASSUME_TAC (Q.SPECL [`v1:'a word`, `d:'a word`] d_lemma4) >>
  full_simp_tac (srw_ss())[] >>
  `n < m` by METIS_TAC[EXP_BASE_LT_MONO,DECIDE ``1 < 2``,w2n_lt] >>
  `?p. m = n + p` by METIS_TAC[LESS_EQ_EXISTS,LESS_IMP_LESS_OR_EQ] >>
  `w2n v1 * 2 ** n < 2 ** p * 2 ** n` by METIS_TAC[d_lemma3,FST,EXP_ADD,MULT_COMM] >>
  POP_ASSUM (fn x => ASSUME_TAC (MP (Q.SPECL [`2 ** p`,`2 ** n`,`w2n (v1:'a word)`] EQ_M_R_S_i) x)) >>
  `2 ** p = 2 ** m DIV 2 ** n` by METIS_TAC[EXP_ADD,MULT_COMM,MULT_DIV,ZERO_LT_EXP,DECIDE ``0 < 2``] >>
  METIS_TAC[ZERO_LT_EXP,DECIDE ``0<2``,ADD1,X_LT_DIV,MULT_COMM]);

val d_clauses = store_thm( "d_clauses",
``!(vs:'a word list) (v1:'a word).
  (0 < w2n v1) ==>
  (0 < w2n (calc_d (v1,1w))) /\
  (mw2n (mw_mul_by_single (calc_d (v1,1w)) (REVERSE (v1::vs))) = mw2n (FRONT (mw_mul_by_single (calc_d (v1,1w)) (REVERSE (v1::vs))))) /\
  (dimword(:'a) DIV 2 <= w2n (LAST (FRONT (mw_mul_by_single (calc_d (v1,1w)) (REVERSE (v1::vs))))))``,

  REPEAT GEN_TAC >> strip_tac >>
  qsuff_tac `0 < w2n (calc_d (v1,1w))`
  THEN1( strip_tac >> strip_tac THEN1 DECIDE_TAC >>
         Q.PAT_ABBREV_TAC `X = mw_mul_by_single (calc_d (v1,1w)) (REVERSE (v1::vs))` >>
         `0 < mw2n X` by ALL_TAC
         THEN1( markerLib.UNABBREV_TAC "X" >>
                REWRITE_TAC[mw_mul_by_single_lemma] >>
                MATCH_MP_TAC ((fn (x,y) => y) (EQ_IMP_RULE (SPEC_ALL (ZERO_LESS_MULT)))) >>
                strip_tac THEN1 DECIDE_TAC >>
                lrw[mw2n_msf] >>
                METIS_TAC[ZERO_LT_EXP,ZERO_LT_dimword,ADD_COMM,LESS_EQ_ADD,LESS_LESS_EQ_TRANS,ZERO_LESS_MULT,dimwords_dimword]) >>
         `X <> []` by METIS_TAC[mw2n_def,NOT_ZERO_LT_ZERO] >>
         qsuff_tac `mw2n X = mw2n (FRONT X)`
         THEN1( qsuff_tac `dimword(:'a) DIV 2 * dimwords (LENGTH vs) (:'a) <= mw2n X`
                THEN1( REPEAT strip_tac THEN1 DECIDE_TAC >>
                       FULL_SIMP_TAC std_ss [] >>
                       `FRONT X <> []` by METIS_TAC[NOT_ZERO_LT_ZERO,mw2n_def] >>
                       `mw2n (FRONT X) = mw2n (FRONT (FRONT X) ++  [LAST (FRONT X)])` by METIS_TAC[APPEND_FRONT_LAST] >>
                       POP_ASSUM (fn x => FULL_SIMP_TAC std_ss [x,mw2n_msf]) >>
                       `LENGTH (FRONT (FRONT X)) = LENGTH (vs:'a word list)` by METIS_TAC[rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE,
                        LENGTH,LENGTH_REVERSE,mw_mul_by_single_lemma,ADD1,Abbr`X`] >>
                        POP_ASSUM (fn x => FULL_SIMP_TAC std_ss [x] \\ ASSUME_TAC x) >>
                       `mw2n (FRONT (FRONT X)) < dimwords (LENGTH (vs:'a word list)) (:'a) ` by METIS_TAC[mw2n_lt]>>
                       `mw2n (FRONT (FRONT X)) + dimwords (LENGTH vs) (:'a) * w2n (LAST (FRONT X))
                        < dimwords (LENGTH vs) (:'a) * (1 + w2n (LAST (FRONT X)))`
                        by METIS_TAC [LESS_MONO_ADD,MULT_RIGHT_1,LEFT_ADD_DISTRIB] >>
                       `dimword(:'a) DIV 2 < SUC (w2n (LAST (FRONT X)))` by METIS_TAC[EQ_M_R_S_i,MULT_COMM,LESS_EQ_LESS_TRANS,ADD1,ADD_COMM] >>
                       DECIDE_TAC) >>
                `mw2n X = w2n (calc_d (v1,1w)) * mw2n (REVERSE (v1::vs))` by METIS_TAC[mw_mul_by_single_lemma,Abbr`X`] >>
                POP_ASSUM (fn x => REWRITE_TAC[x]) >>
                srw_tac[][mw2n_msf,LEFT_ADD_DISTRIB] >>
                REWRITE_TAC[DECIDE ``a*b + a * (c * d) = a*d*c + a*b``] >>
                `v1 <> 0w` by (Cases_on `v1 = 0w` >> full_simp_tac (srw_ss())[]) >>
                `!(a:'a word) (b:'a word).w2n (a * b) <= w2n a * w2n b` by srw_tac[][word_mul_def,MOD_LESS_EQ] >>
                METIS_TAC[d_lemma2,FST,LESS_MONO_MULT,LESS_EQ_ADD,LESS_EQ_TRANS]) >>
         MATCH_MP_TAC mw2n_msf_NIL >> strip_tac THEN1 METIS_TAC[] >>
         srw_tac[][rich_listTheory.LENGTH_BUTLAST] >>
         markerLib.UNABBREV_TAC "X" >>
         REWRITE_TAC[mw_mul_by_single_lemma,GSYM ADD1,prim_recTheory.PRE] >>
         Q.PAT_ABBREV_TAC `Z = w2n (calc_d (v1,1w))` >>
         Cases_on `Z = 1` THEN1 METIS_TAC[mw2n_lt,DECIDE``1*x = x``] >>
         full_simp_tac (srw_ss())[mw2n_msf,LEFT_ADD_DISTRIB] >>
         REWRITE_TAC[DECIDE ``x*y + x*(z*w) = x*w*z + x*y``,EXP] >>
         Q.PAT_ABBREV_TAC `Y = Z * w2n v1 * dimwords (LENGTH vs) (:'a)` >>
         Cases_on `v1 = 0w` THEN1 METIS_TAC[word_0_n2w,DECIDE ``~(0<0)``] >>
         `0 < Z` by METIS_TAC[FST,d_lemma2_bis,NOT_0w_bis] >>
         `2 <= Z` by DECIDE_TAC >>
         MATCH_MP_TAC LESS_LESS_EQ_TRANS >>
         EXISTS_TAC ``Y + Z * dimwords (LENGTH (vs:'a word list)) (:'a)`` >> strip_tac THEN1
         METIS_TAC[LESS_MONO_ADD,ADD_COMM,MULT_COMM,mw2n_lt,LENGTH_REVERSE,LT_MULT_RCANCEL] >>
         markerLib.UNABBREV_TAC "Y" >>
         REWRITE_TAC[dimwords_SUC,DECIDE ``z*v*l + z*l = z*(v+1)*l``,DECIDE ``x * dimword(:'a) = dimword(:'a) * x``] >>
         MATCH_MP_TAC LESS_MONO_MULT >> METIS_TAC[Abbr`Z`,ADD1,d_lemma5,FST,MULT_COMM]) >>
  Cases_on `v1 = 0w` THEN1 full_simp_tac (srw_ss())[] >> METIS_TAC[d_lemma2_bis,FST,NOT_0w_bis])

val LAST_FRONT_mw_mul_by_single_NOT_ZERO = store_thm(
   "LAST_FRONT_mw_mul_by_single_NOT_ZERO",
  ``mw_ok ys /\ ys <> [] /\ 2 < dimword (:'a)  ==>
    LAST (FRONT (mw_mul_by_single (calc_d (LAST ys,0x1w:'a word)) ys)) <> 0x0w``,
  STRIP_TAC
  \\ MP_TAC (d_clauses |> Q.SPECL [`TL (REVERSE ys)`,`HD (REVERSE ys)`])
  \\ `~(NULL (REVERSE ys))` by FULL_SIMP_TAC std_ss [NULL_EQ,REVERSE_EQ_NIL]
  \\ FULL_SIMP_TAC std_ss [CONS,NULL_DEF,REVERSE_REVERSE]
  \\ FULL_SIMP_TAC std_ss [HD_REVERSE]
  \\ Cases_on `LAST (FRONT (mw_mul_by_single (calc_d (LAST ys,0x1w)) ys))`
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,DIV_LE_X,n2w_11,ZERO_LT_dimword,mw_ok_def]
  \\ Cases_on `LAST ys`
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,DIV_LE_X,n2w_11,ZERO_LT_dimword,mw_ok_def]
  \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ DECIDE_TAC);

(* Single Division: x1x2 / y *)

val single_div_lemma1 = store_thm ( "single_div_lemma1" ,
`` w2n (x1:'a word) < w2n (y:'a word) ==>
   (w2n (x2:'a word) +  dimword(:'a) * w2n x1) DIV w2n y < dimword(:'a)``,
  strip_tac >> MATCH_MP_TAC DIV_thm2 >> strip_tac THEN1 DECIDE_TAC >>
  `w2n x2 < dimword(:'a)` by METIS_TAC[w2n_lt] >>
  `w2n x2 + dimword(:'a) * w2n x1 < dimword(:'a) * SUC (w2n x1)`
  by METIS_TAC[LESS_MONO_ADD,MULT_RIGHT_1,LEFT_ADD_DISTRIB,ADD1,ADD_COMM] >>
  METIS_TAC[LESS_EQ,LESS_LESS_EQ_TRANS,LESS_MONO_MULT,MULT_COMM] );

val single_div_lemma2 = store_thm ( "single_div_lemma2",
  ``y <> 0w ==> w2n (SND (single_div x1 x2 y)) < w2n y``,
  lrw[single_div_def] >>
  ` 0 < w2n y` by PROVE_TAC [NOT_0w_bis] >>
  `0 < dimword(:'a)` by PROVE_TAC[ZERO_LT_dimword] >>
  Q.PAT_ABBREV_TAC`x = w2n x2 + dimword (:'a) * w2n x1` >>
  Q.PAT_ABBREV_TAC`z = x MOD w2n y` >>
  `z < w2n y` by PROVE_TAC[MOD_LESS] >>
  `z MOD dimword(:'a) <= z` by PROVE_TAC[MOD_LESS_EQ] >>
  DECIDE_TAC);

val single_div_thm = store_thm ( "single_div_thm",
  ``!(x1:'a word) (x2:'a word) y q r. (single_div x1 x2 y = (q,r))
    ==>(((w2n x1 * dimword(:'a) + w2n x2) DIV w2n y < dimword(:'a) /\
          y <> 0w)
    ==> ((w2n q = (w2n x1 * dimword(:'a) + w2n x2) DIV w2n y) /\
         (w2n r = (w2n x1 * dimword(:'a) + w2n x2) MOD w2n y)))``,

  lrw[single_div_def] >> full_simp_tac (srw_ss()) [] >> lrw[w2n_n2w] >>
  `!w. w <> 0w ==> 0 < w2n w` by (Cases_on `w`>> full_simp_tac (srw_ss()) [] >> DECIDE_TAC) >>
  `w2n y < dimword(:'a)` by lrw[w2n_lt] >>
  METIS_TAC[MOD_LESS,LESS_TRANS] );

val single_div_thm_bis = store_thm ( "single_div_thm_bis",
  ``!(x1:'a word) (x2:'a word) y q r. (single_div x1 x2 y = (q,r)) /\
    (w2n x1 < w2n y) ==>
    (w2n q * w2n y + w2n r = w2n x1 * dimword(:'a) + w2n x2)``,

    REPEAT strip_tac >> IMP_RES_TAC single_div_lemma1 >>
    qpat_x_assum `!xs. xxx` (fn x => (ASSUME_TAC (RW[Once ADD_COMM,Once MULT_COMM] (SPEC ``x2:'a word`` x)))) >>
    Cases_on `y = 0w` THEN1 full_simp_tac (srw_ss())[word_0_n2w] >>
    IMP_RES_TAC single_div_thm >> `0 < w2n y` by DECIDE_TAC >>
    METIS_TAC[DIVISION]);

(* Division by single: x_{1}x_{2}...x_{n} / y  *)

val mw_div_by_single_LENGTH = store_thm ("mw_div_by_single_LENGTH",
``!x xs y. w2n x < w2n y ==>
    (LENGTH (mw_div_by_single (x::xs) y) = SUC (LENGTH xs))``,

  REPEAT GEN_TAC >>
  completeInduct_on `LENGTH (x::xs)`>>
  REPEAT STRIP_TAC >>
  Cases_on `xs` THEN1 lrw[Once mw_div_by_single_def,single_div_def] >>
  lrw[Once mw_div_by_single_def,single_div_def] >>
  Q.PAT_ABBREV_TAC `w:'a word = n2w ((w2n h + dimword (:'a) * w2n x) MOD w2n y)` >>
  `w2n w < w2n y` by ALL_TAC
  THEN1 (markerLib.UNABBREV_TAC "w" >>
         REWRITE_TAC[w2n_n2w] >>
         METIS_TAC[DECIDE ``!a. 0 <= a``,LESS_EQ_LESS_TRANS,MOD_LESS_EQ,MOD_LESS,ZERO_LT_dimword]) >>
  METIS_TAC[LENGTH, DECIDE ``n < SUC n``])

val mw_div_by_single_thm = store_thm ( "mw_div_by_single_thm",
``!xs y. 0 < w2n y ==> (mw2n (REVERSE xs) = mw2n (mw_mul_by_single y (REVERSE (FRONT (mw_div_by_single xs y)))) + w2n (LAST (mw_div_by_single xs y)))``,

HO_MATCH_MP_TAC mw_div_by_single_ind >>
REPEAT strip_tac
THEN1 (srw_tac[][Once mw_div_by_single_def] >> srw_tac[][mw_div_by_single_def,mw_mul_by_single_def,mw_mul_pass_def,mw2n_def])
THEN1 (srw_tac[][single_div_def,mw_mul_by_single_lemma,mw_div_by_single_def,mw2n_def] >>
       METIS_TAC[MULT_COMM,DIVISION,w2n_lt,LESS_MOD,MOD_LESS_EQ,DIV_LESS_EQ,LESS_EQ_LESS_TRANS]) >>
Cases_on `(w2n x1 < w2n y \/ (w2n y = 0))` >>
Q.PAT_ABBREV_TAC `rxs = REVERSE (x1::x2::xs)` >>
srw_tac[][Once mw_div_by_single_def]
THENL [ALL_TAC,full_simp_tac (srw_ss())[],ALL_TAC]
THEN1 (`(mw2n (REVERSE (r::xs)) = mw2n (mw_mul_by_single y (REVERSE (FRONT (mw_div_by_single (r::xs) y)))) + w2n (LAST (mw_div_by_single (r::xs) y)))` by METIS_TAC[] >>
       REPEAT (qpat_x_assum `!q r. xxx` (K ALL_TAC)) >>
       srw_tac[][Once mw_div_by_single_def] >>
       `w2n r < w2n y` by ALL_TAC
       THEN1 ( full_simp_tac (srw_ss())[single_div_def] >>
             qpat_x_assum `xxx=r` (fn x => REWRITE_TAC[GSYM x]) >>
             srw_tac[][w2n_n2w] >>
             METIS_TAC[LESS_EQ_LESS_TRANS,MOD_LESS_EQ,MOD_LESS,ZERO_LT_dimword]) >>
       `mw_div_by_single (r::xs) y <> []` by
       METIS_TAC[mw_div_by_single_LENGTH,NOT_NIL_EQ_LENGTH_NOT_0,DECIDE ``0 < SUC n``] >>
       srw_tac[][LAST_DEF,FRONT_DEF,mw2n_msf,mw_mul_by_single_lemma] >>
       `mw2n rxs = mw2n (REVERSE (r::xs)) + w2n q * w2n y * dimwords (LENGTH xs) (:'a)` by ALL_TAC
       THEN1(markerLib.UNABBREV_TAC "rxs" >>
             qpat_x_assum `mw2n (REVERSE xx) = yy` (K ALL_TAC) >>
             lrw[mw2n_msf] >>
             REWRITE_TAC[dimwords_dimword] >>
             REWRITE_TAC[GSYM ADD1, EXP,
               DECIDE ``a1 * (d * l) + a2 * l = (a1 * d + a2)*l``,
               DECIDE ``b * l + d * e * l = (d * e + b)*l``] >>
             METIS_TAC[single_div_thm_bis]) >>
       ASM_SIMP_TAC std_ss [mw_mul_by_single_lemma] >>
       `LENGTH (FRONT (mw_div_by_single (r::xs) y)) = LENGTH xs` by
       METIS_TAC[mw_div_by_single_LENGTH,DECIDE ``0 < SUC n``,NOT_NIL_EQ_LENGTH_NOT_0,rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
       RW_TAC arith_ss[]) >>
`mw2n (REVERSE (r::x2::xs)) = mw2n (mw_mul_by_single y (REVERSE (FRONT (mw_div_by_single (r::x2::xs) y)))) + w2n (LAST (mw_div_by_single (r::x2::xs) y))` by METIS_TAC[] >>
REPEAT (qpat_x_assum `!q r. xxx` (K ALL_TAC)) >>
`mw2n rxs = mw2n (REVERSE (r::x2::xs)) + w2n q * w2n y * dimwords (SUC(LENGTH xs)) (:'a)` by ALL_TAC
THEN1 (markerLib.UNABBREV_TAC "rxs" >>
       qpat_x_assum `mw2n (REVERSE xx) = yy` (K ALL_TAC) >>
       lrw[mw2n_msf,GSYM ADD1,EXP] >>
       `w2n x1 = w2n r + w2n q * w2n y` by ALL_TAC
       THEN1 (IMP_RES_TAC single_div_thm_bis >> ASSUME_TAC word_0_n2w >>
              FULL_SIMP_TAC arith_ss []) >>
RW_TAC arith_ss[]) >>
`(mw_div_by_single (x1::x2::xs) y) = q::mw_div_by_single (r::x2::xs) y` by srw_tac[][Once mw_div_by_single_def] >>
POP_ASSUM (fn x => REWRITE_TAC[x]) >>
`w2n r < w2n y` by ALL_TAC
THEN1 ( full_simp_tac (srw_ss())[single_div_def] >>
      qpat_x_assum `xxx=r` (fn x => REWRITE_TAC[GSYM x]) >>
      srw_tac[][w2n_n2w] >>
      METIS_TAC[LESS_EQ_LESS_TRANS,MOD_LESS_EQ,MOD_LESS,ZERO_LT_dimword]) >>
`mw_div_by_single (r::x2::xs) y <> []` by
METIS_TAC[mw_div_by_single_LENGTH,NOT_NIL_EQ_LENGTH_NOT_0,DECIDE ``0 < SUC n``] >>
lrw[mw_mul_by_single_lemma,FRONT_DEF,LAST_DEF,mw2n_msf] >>
`LENGTH (FRONT (mw_div_by_single (r::x2::xs) y)) = SUC (LENGTH xs)` by
METIS_TAC[mw_div_by_single_LENGTH,DECIDE ``0 < SUC n``,LENGTH,NOT_NIL_EQ_LENGTH_NOT_0,rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
RW_TAC arith_ss[])

val mw_div_by_single_thm_bis = store_thm ("mw_div_by_single_thm_bis",
``!xs y. 0 < w2n y ==>
  (mw2n (REVERSE (FRONT (mw_div_by_single xs y))) = mw2n (REVERSE xs) DIV w2n y) /\
  (w2n (LAST (mw_div_by_single xs y)) = mw2n (REVERSE xs) MOD w2n y)``,

  qsuff_tac `! (xs:'a word list) (y:'a word). 0 < w2n y ==>
               w2n (LAST (mw_div_by_single xs y)) < w2n y`
  THEN1( REPEAT strip_tac >>
         IMP_RES_TAC mw_div_by_single_thm >>
         POP_ASSUM (fn x => ASSUME_TAC (Q.SPECL [`xs:'a word list`] x)) >>
         FULL_SIMP_TAC std_ss [mw_mul_by_single_lemma] >>
         ONCE_REWRITE_TAC[MULT_COMM] >>
         srw_tac[][MOD_TIMES,ADD_DIV_ADD_DIV] >>
         MATCH_MP_TAC ((fn (x,y) => y) (EQ_IMP_RULE (SPEC_ALL EQ_ADDL))) >>
         MATCH_MP_TAC LESS_DIV_EQ_ZERO >> METIS_TAC[]) >>

  HO_MATCH_MP_TAC mw_div_by_single_ind >>
  REPEAT strip_tac
   THEN1 lrw[mw_div_by_single_def]
  THEN1( lrw[mw_div_by_single_def,single_div_def] >>
         METIS_TAC[MOD_LESS,LESS_EQ_LESS_TRANS,MOD_LESS_EQ,ZERO_LT_dimword]) >>
  srw_tac[][Once mw_div_by_single_def]
  THENL[Q.PAT_ABBREV_TAC `w = r::xs`,METIS_TAC[word_0_n2w,NOT_ZERO_LT_ZERO],Q.PAT_ABBREV_TAC `w = r::x2::xs`] >>
  `w2n r < w2n y` by
         ( FULL_SIMP_TAC std_ss [single_div_def] >>
           POP_ASSUM (fn x => REWRITE_TAC[GSYM x]) >>
           srw_tac[][] >>
           METIS_TAC[MOD_LESS,LESS_EQ_LESS_TRANS,MOD_LESS_EQ,ZERO_LT_dimword]) >>
  `mw_div_by_single w y <> []` by METIS_TAC[DECIDE ``0 < SUC x``,NOT_NIL_EQ_LENGTH_NOT_0,mw_div_by_single_LENGTH] >>
  markerLib.UNABBREV_TAC "w" >>
  srw_tac[][listTheory.LAST_CONS_cond,word_0_n2w] >>
  METIS_TAC[w2n_eq_0])

val mw_simple_div_lemma = prove(
  ``!xs x y qs (r:'a word) c.
      (mw_simple_div x xs y = (qs,r,c)) /\ 0w <+ y /\ x <+ y ==>
      (mw_div_by_single (x::xs) y = SNOC r qs) /\ c``,
  Induct THEN1
   (FULL_SIMP_TAC std_ss [mw_simple_div_def,mw_div_by_single_def,WORD_LO]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `single_div 0x0w x y` \\ FULL_SIMP_TAC std_ss [SNOC,CONS_11]
    \\ IMP_RES_TAC single_div_thm_bis
    \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
    \\ Cases_on `w2n q` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
    \\ Cases_on `r` \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
    \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [Once mw_simple_div_def,Once mw_div_by_single_def,WORD_LO]
  \\ NTAC 5 STRIP_TAC
  \\ Cases_on `single_div x h y` \\ SIMP_TAC std_ss [LET_DEF]
  \\ `?qs r1 c1. mw_simple_div r' xs y = (qs,r1,c1)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [SNOC,CONS_11] \\ STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Q.PAT_X_ASSUM `!x.bb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [WORD_LO]
  \\ `y <> 0w` by (Cases_on `y` \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ `(w2n x * dimword (:'a) + w2n h) DIV w2n y < dimword (:'a)` by ALL_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [DIV_LT_X]
    \\ MATCH_MP_TAC LESS_LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `SUC (w2n x) * dimword (:'a)` \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [MULT_CLAUSES] \\ Cases_on `h`
      \\ FULL_SIMP_TAC (srw_ss()) [DIV_LT_X])
    \\ SIMP_TAC std_ss [Once MULT_COMM]
    \\ DECIDE_TAC)
  \\ IMP_RES_TAC single_div_thm \\ FULL_SIMP_TAC (srw_ss()) []);

val mw2n_SNOC_0 = Q.prove(
  `!xs. mw2n (SNOC 0w xs) = mw2n xs`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [mw2n_def,SNOC]);

val mw_simple_div_thm = store_thm("mw_simple_div_thm",
  ``!xs y qs (r:'a word) c.
      (mw_simple_div 0w xs y = (qs,r,c)) /\ 0w <+ y ==>
      (mw2n (REVERSE qs) = mw2n (REVERSE xs) DIV w2n y) /\
      (w2n r = mw2n (REVERSE xs) MOD w2n y) /\ c``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC mw_simple_div_lemma
  \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO]
  \\ IMP_RES_TAC mw_div_by_single_thm_bis
  \\ REPEAT (Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `0w::xs`))
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC,mw2n_SNOC_0]);


(* multiWord Division: x_{1}_x{2}...x_{m+n} / y_{1}...y_{n} *)

(* Following the proof on p.271 *)

val mw_div_range1 = Q.store_thm("mw_div_range1",
  `! (u1:'a word) u2 us (v1:'a word) vs.
    (LENGTH us = LENGTH vs) /\
    0 < w2n v1 /\
    mw2n (REVERSE (u1::u2::us)) DIV mw2n (REVERSE (v1::vs))
    < dimword(:'a) ==>
    MIN ((w2n u1 * dimword(:'a) + w2n u2) DIV w2n v1) (dimword(:'a)-1)
    >= mw2n (REVERSE (u1::u2::us)) DIV mw2n (REVERSE (v1::vs))`,

    REPEAT GEN_TAC >>
    Q.PAT_ABBREV_TAC`Q = (w2n u1 * dimword (:'a) + w2n u2) DIV w2n v1` >>
    Q.PAT_ABBREV_TAC`X = mw2n (REVERSE (u1::u2::us)) DIV mw2n (REVERSE (v1::vs))` >>
    REPEAT strip_tac >>
    Cases_on `Q < (dimword(:'a) - 1)` >> lrw[MIN_DEF] >>
    markerLib.UNABBREV_TAC"X">>
    `0 < mw2n (REVERSE (v1::vs))` by
    (full_simp_tac (srw_ss())[mw2n_msf] >> METIS_TAC[dimwords_dimword,ZERO_LT_dimword,ZERO_LT_EXP,LE_MULT_CANCEL_LBARE,LESS_LESS_EQ_TRANS,ADD_COMM,LESS_EQ_ADD,LESS_EQ_TRANS]) >>
    MATCH_MP_TAC DIV_thm5 >> strip_tac THEN1 DECIDE_TAC >>
    markerLib.UNABBREV_TAC "Q" >>
    Q.PAT_ABBREV_TAC`a=(w2n u1) * dimword(:'a) + w2n u2`>>
    lrw[mw2n_msf,dimwords_dimword] >>
    Q.PAT_ABBREV_TAC`V1= w2n v1` >>
    Q.PAT_ABBREV_TAC`U1 = w2n u1` >>
    Q.PAT_ABBREV_TAC`U2 = w2n u2` >>
    full_simp_tac (srw_ss())[] >>
    `a + 1 <= V1 + a DIV V1 * V1`
    by METIS_TAC[DIV_thm4,LESS_MONO_ADD,DIV_thm3,SUB_ADD,LESS_EQ,ADD1] >>
    Q.PAT_ABBREV_TAC`q=a DIV V1` >>
    REWRITE_TAC[GSYM ADD1,EXP] >>
    Q.PAT_ABBREV_TAC`offset= dimword(:'a) ** (LENGTH t)` >>
    MATCH_MP_TAC (METIS_PROVE [ADD_COMM,LESS_EQ_ADD,LESS_LESS_EQ_TRANS] ``(a < b) ==> (a < c + b)``) >>
    REWRITE_TAC[RIGHT_ADD_DISTRIB] >>
    ONCE_REWRITE_TAC[METIS_PROVE [ADD_ASSOC,ADD_COMM] ``a + (b + c) = b + (a + c)``] >>
    MATCH_MP_TAC (METIS_PROVE [ADD_COMM,LESS_EQ_ADD,LESS_LESS_EQ_TRANS] ``(a < b) ==> (a < c + b)``) >>
    RW_TAC arith_ss [] >>
    ONCE_REWRITE_TAC[DECIDE ``a*b*c = a*c*b``] >> REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] >>
    `offset * (a + 1) <= offset * (V1 + q * V1)` by METIS_TAC[LESS_MONO_MULT,MULT_COMM] >>
    MATCH_MP_TAC LESS_LESS_EQ_TRANS >>
    EXISTS_TAC ``offset * (a + 1)`` >> lrw[] >>
    `U2 + U1 * dimword(:'a) = a` by METIS_TAC[Abbr`a`,ADD_COMM] >>
    ASM_REWRITE_TAC[] >> REWRITE_TAC[LEFT_ADD_DISTRIB] >> RW_TAC arith_ss[] >>
    METIS_TAC[LENGTH_REVERSE,mw2n_lt,Abbr `offset`,dimwords_dimword]);

(* Proof on p.271-272 *)

val mw_div_range2 = Q.store_thm( "mw_div_range2",
  `! (u1:'a word) u2 us (v1:'a word) vs.
    (LENGTH us = LENGTH vs) /\
    mw2n (REVERSE (u1::u2::us)) DIV mw2n (REVERSE (v1::vs))
    < dimword(:'a) /\
    dimword(:'a) DIV 2 <= w2n v1 ==>
    MIN ((w2n u1 * dimword(:'a) + w2n u2) DIV w2n v1) (dimword(:'a)-1)
    <= mw2n (REVERSE (u1::u2::us)) DIV mw2n (REVERSE (v1::vs)) + 2`,

    REPEAT GEN_TAC >>
    Q.PAT_ABBREV_TAC`V = mw2n (REVERSE (v1::vs))` >>
    Q.PAT_ABBREV_TAC`U = mw2n (REVERSE (u1::u2::us))`>>
    Q.PAT_ABBREV_TAC`q = U DIV V` >>
    Q.PAT_ABBREV_TAC`q' = MIN ((w2n u1 * dimword(:'a) + w2n u2) DIV w2n v1) (dimword(:'a) - 1)` >>
    Cases_on `V <= U`
    THEN1( (MATCH_MP_TAC o (fn (x,y) => y)) (EQ_IMP_RULE MONO_NOT_EQ) >>
           strip_tac >>
           qpat_x_assum `~x` (ASSUME_TAC o (fn x => (MP ((fn (x,y)=>x) (EQ_IMP_RULE (Q.SPECL [`q'`,`q+2`] NOT_LESS_EQUAL)))  x))) >>
           Cases_on `LENGTH us = LENGTH vs`
           THEN1( Cases_on `q < dimword(:'a)`
                  THEN1( srw_tac[][] >> REWRITE_TAC [NOT_LESS_EQUAL] >>
                         `3 <= q' - q` by METIS_TAC[SUB_LEFT_LESS,ADD_COMM,LESS_EQ,DECIDE ``3 = SUC 2``] >>
                         Q.PAT_ABBREV_TAC`b = dimword(:'a)` >> REWRITE_TAC[HD] >>
                         Cases_on `0 < w2n v1`
                         THEN1( Q.PAT_ABBREV_TAC`a = w2n v1` >>
                                `0 < b ** LENGTH vs` by METIS_TAC[Abbr`b`,ZERO_LT_dimword,ZERO_LT_EXP] >>
                                `0 < V` by (lrw[Abbr`V`,Abbr`a`,mw2n_msf,dimwords_dimword] >> METIS_TAC[ADD_COMM,MULT_COMM,LESS_EQ_ADD,LE_MULT_CANCEL_LBARE,LESS_EQ_TRANS,LESS_LESS_EQ_TRANS]) >>
                                `b ** (LENGTH vs ) <= V` by (lrw[Abbr`V`,mw2n_msf,LENGTH_REVERSE,dimwords_dimword] >> METIS_TAC[LE_MULT_CANCEL_LBARE,LESS_EQ_ADD,ADD_COMM,LESS_EQ_TRANS]) >>
                                Cases_on `V = b ** (LENGTH vs)`
                                THEN1( `V = mw2n ((REVERSE vs)++[v1])` by full_simp_tac (srw_ss())[] >>
                                       qpat_x_assum `V = mw2n xxx` (fn x => (ASSUME_TAC (RW[mw2n_msf,LENGTH_REVERSE,dimwords_dimword] x))) >>
                                       `b ** LENGTH vs * w2n v1 <= V` by METIS_TAC[ADD_COMM,LESS_EQ_ADD] >>
                                       `0 < b ** LENGTH vs` by METIS_TAC[ZERO_LT_EXP,Abbr`b`,ZERO_LT_dimword] >>
                                       `a <= 1` by METIS_TAC[Abbr`a`,LE_MULT_CANCEL_RBARE,NOT_ZERO_LT_ZERO] >>
                                       `a = 1` by DECIDE_TAC  >>
                                       `U = mw2n (REVERSE us) + V*(w2n u2) + V*b*(w2n u1)` by full_simp_tac (srw_ss())[MULT_COMM,Abbr`b`,Abbr`U`,LENGTH_REVERSE,mw2n_msf,dimwords_dimword,GSYM ADD1,EXP] >>
                                       qpat_x_assum `U = xxx` (fn x => ASSUME_TAC(RW[GSYM MULT_ASSOC,GSYM ADD_ASSOC,GSYM LEFT_ADD_DISTRIB] x)) >>
                                       `mw2n (REVERSE us) < V` by METIS_TAC[mw2n_lt,dimwords_dimword,Abbr`b`,LENGTH_REVERSE] >>
                                       `q = w2n u1 * b + w2n u2` by METIS_TAC[RIGHT_ADD_DISTRIB,DIV_MULT,ADD_COMM,MULT_COMM] >>
                                       `q' = MIN (b-1) q` by full_simp_tac (srw_ss())[MIN_COMM] >>
                                       `~(b - 1 < q)` by DECIDE_TAC >>
                                       `q' = q` by full_simp_tac (srw_ss())[MIN_DEF] >>
                                       RW_TAC arith_ss [] ) >>
                                `b ** (LENGTH vs) < V` by DECIDE_TAC >>
                                qpat_x_assum `xxx <> yyy` (fn x => ALL_TAC) >>
                                `2 * V * (V - b ** (LENGTH vs)) <= U * b ** (LENGTH vs)` by ALL_TAC
                                THEN1( Q.PAT_ABBREV_TAC`l = b ** LENGTH vs` >>
                                       `l < V` by METIS_TAC[LE_MULT_CANCEL_LBARE,LESS_EQ_LESS_TRANS] >>
                                       Q.PAT_ABBREV_TAC`X= V - l` >> `0 < X` by METIS_TAC[SUB_LESS_0] >>
                                       `0 < l` by METIS_TAC[ZERO_LT_dimword,ZERO_LT_EXP] >>
                                       `0 < q*V` by METIS_TAC[DIV_GT0,ZERO_LESS_MULT] >>
                                       `U - V < q * V + V - V` by METIS_TAC[DIV_thm4,DIV_thm3,LESS_MONO_ADD,SUB_ADD,ADD_COMM,LT_SUB_RCANCEL,ADD_0] >>
                                       qpat_x_assum `U - V < xxx` (fn x => ASSUME_TAC ( METIS_PROVE[x,ADD_SUB] ``U-V < q*V``)) >>
                                       `q' <= (w2n u1 * b + w2n u2) DIV a` by lrw[Abbr`a`,Abbr`q'`] >>
                                       `q' * (a * l) <= (w2n u1 * b + w2n u2) * l` by METIS_TAC[MULT_ASSOC,Abbr`a`,DIV_thm3,LESS_EQ_TRANS,LESS_MONO_MULT,Abbr`q'`] >>
                                       `U = (w2n u1 * b + w2n u2) * l + mw2n (REVERSE us)` by lrw[Abbr`U`,Abbr`b`,Abbr`l`,mw2n_msf,dimwords_dimword,EXP,GSYM ADD1] >>
                                       `q' * (a * l) <= U` by METIS_TAC[Abbr`a`,LESS_EQ_ADD,LESS_EQ_TRANS,Abbr`q'`] >>
                                       Cases_on `U = 0` THEN1 full_simp_tac (srw_ss())[] >>
                                       `q' * X < U` by ALL_TAC
                                       THEN1( Cases_on `0 < q'`
                                              THEN1( `V = a * l + mw2n(REVERSE vs)` by lrw[Abbr`V`,Abbr`l`,Abbr`a`,mw2n_msf,dimwords_dimword] >>
                                                     `V < a * l + l` by (full_simp_tac (srw_ss())[Abbr`l`,Abbr`b`,Abbr`a`] >> METIS_TAC[mw2n_lt,LENGTH_REVERSE,dimwords_dimword]) >>
                                                     `0 < a * l` by METIS_TAC[ZERO_LT_EXP,ZERO_LT_dimword, Abbr`a`,ZERO_LESS_MULT] >>
                                                     `X < a * l` by full_simp_tac (srw_ss())[Abbr`X`,ADD_SUB,LT_SUB_RCANCEL,LT_ADDL,ADD_COMM] >>
                                                     METIS_TAC[LT_MULT_RCANCEL,MULT_COMM,LESS_LESS_EQ_TRANS]) >>
                                              DECIDE_TAC) >>
                                       qpat_x_assum `q' <= xxx` (fn x => ALL_TAC)>>
                                       REPEAT (qpat_x_assum `q' * (a * l) <= xxx` (fn x => ALL_TAC)) >>
                                       `3 * (X * V) <= q' * (X * V) - q * (X * V) /\
                                       (q' * (X * V) < U * V) /\
                                       ((U - V) * X < q * (V * X))`
                                       by METIS_TAC[LESS_MONO_MULT,RIGHT_SUB_DISTRIB,LT_MULT_RCANCEL,MULT_ASSOC] >>
                                       `3 * (X * V) <= U * V - (U-V)*X` by DECIDE_TAC >>
                                       markerLib.UNABBREV_TAC "X" >>
                                       `3 * ((V-l)*V) <= U*V - ((U-V)*V - (U-V)*l)` by METIS_TAC[LEFT_SUB_DISTRIB] >>
                                       `(U-V)*l <= (U-V)*V` by METIS_TAC[LESS_IMP_LESS_OR_EQ,LE_MULT_LCANCEL] >>
                                       `3 * ((V-l)*V) <= U*V + (U-V)*l - (U-V)*V` by METIS_TAC[SUB_SUB] >>
                                       `3 * ((V-l)*V) <= U*V + (U*l - V*l) - (U*V - V*V)` by METIS_TAC[RIGHT_SUB_DISTRIB]>>
                                       `3 * ((V-l)*V) <= U*V + (U*l - V*l) + V*V - U*V`by METIS_TAC[LE_MULT_RCANCEL,SUB_SUB] >>
                                       `3 * ((V-l)*V) <= U*l - V*l + V*V` by METIS_TAC[ADD_ASSOC,PROVE [ADD_COMM,ADD_ASSOC,ADD_SUB] ``a+b-a=b``]>>
                                       `V*l <= U*l` by METIS_TAC[LESS_MONO_MULT] >>
                                       `3*((V-l)*V) <= (V*V + U*l) - V*l` by METIS_TAC[ADD_COMM,LESS_MONO_MULT,LESS_EQ_ADD_SUB] >>
                                       `3*((V-l)*V) <= U*l + V*(V-l)` by METIS_TAC[ADD_COMM,LEFT_SUB_DISTRIB,LESS_EQ_ADD_SUB,SUB_LESS_0,LESS_IMP_LESS_OR_EQ,LE_MULT_LCANCEL] >>
                                       qpat_x_assum `xxx <= yyy + V*(V-l)` (fn x =>
                                                   ASSUME_TAC (RW[DECIDE ``3 = 2 + 1``,RIGHT_ADD_DISTRIB,MULT_LEFT_1] x)) >>
                                       `(V-l)*V <= V*V` by METIS_TAC[SUB_LESS_EQ,LESS_MONO_MULT] >>
                                       REPEAT (qpat_x_assum `3*xxx <= yyy` (fn x => ALL_TAC)) >>
                                       METIS_TAC[MULT_COMM,MULT_ASSOC,LESS_EQ_MONO_ADD_EQ]) >>
                               `V = (a-1+1) * b ** LENGTH vs + mw2n(REVERSE vs)` by lrw[Abbr`V`,Abbr`a`,mw2n_msf,dimwords_dimword] >>
                               qpat_x_assum `V = xxx` (fn x => (ASSUME_TAC (RW[RIGHT_ADD_DISTRIB,MULT_LEFT_1,Once (DECIDE ``a + b + c = a + c + b``)] x))) >>
                               `(a - 1) * b ** (LENGTH vs) <= V - b ** (LENGTH vs)`  by METIS_TAC[ADD_SUB,LESS_EQ_ADD] >>
                               `2 * V * ((a-1) * b ** LENGTH vs) <= 2 * V * (V - b ** LENGTH vs)` by full_simp_tac (srw_ss())[] >>
                               `2 * V * ((a-1) * b ** LENGTH vs) <= U * b ** LENGTH vs` by METIS_TAC[LESS_EQ_TRANS] >>
                               qpat_x_assum `xxx <= U * b ** LENGTH vs` (fn x => ASSUME_TAC (RW[MULT_ASSOC] x)) >>
                               `b ** LENGTH vs <> 0` by METIS_TAC[ZERO_LT_EXP,Abbr`b`,ZERO_LT_dimword,NOT_ZERO_LT_ZERO] >>
                               `2 * V * (a-1) <= U` by METIS_TAC[LE_MULT_RCANCEL] >>
                               qpat_x_assum `2 * V * xxx <= U` (fn x => (ASSUME_TAC (RW[Once (DECIDE ``a * b * c = a * c * b``)] x))) >>
                               `2 * (a-1) <= q` by METIS_TAC[Abbr`q`,DIV_LE_MONOTONE,MULT_DIV] >>
                               `q + 3 <= q'` by METIS_TAC [LESS_EQ, EVAL ``SUC 2``,ADD,ADD_COMM] >>
                               `q <= (q' - 3)` by METIS_TAC[LE_SUB_RCANCEL,ADD_SUB,ADD_COMM,LESS_EQ_ADD] >>
                               qpat_x_assum ` q + 3 <= q'` (fn x => ALL_TAC) >>
                               `!xx yy.MIN xx yy <= yy` by srw_tac[][] >>
                               `q' <= b - 1` by METIS_TAC[] >> qpat_x_assum `!xx yy. zzz` (fn x => ALL_TAC) >>
                               `2 <= b - 2` by METIS_TAC[SUB_LESS_EQ,LESS_EQ_TRANS,LE_SUB_RCANCEL,DECIDE ``(3-1 = 2)/\(b - 1 - 1 = b - 2)``]  >>
                               `2 <= 2 * a` by METIS_TAC[LE_MULT_CANCEL_LBARE,Abbr`a`] >>
                               `q' - 3 <= b - 4` by  METIS_TAC[LE_SUB_RCANCEL,SUB_LESS_EQ,LESS_EQ_TRANS,DECIDE ``x - 1 - 3 = x - 4``] >>
                               `2 * a <= b - 2` by RW_TAC arith_ss [] >>
                               qpat_x_assum `2*a <= xxx` (ASSUME_TAC o (fn x => (METIS_PROVE [DIV_LE_MONOTONE, DECIDE ``0<2``, MULT_COMM,MULT_DIV,x] ``a <= (b - 2) DIV 2``))) >>
                               `2 <= b` by METIS_TAC[SUB_LESS_EQ, LESS_EQ_TRANS] >>
                               `a <= (b DIV 2 - 1)` by METIS_TAC[DECIDE ``0<2``,MULT_RIGHT_1,DIV_SUB] >>
                               RW_TAC arith_ss [Abbr`b`,ZERO_LT_dimword] ) >>
                       `w2n v1 = 0` by DECIDE_TAC >>
                       METIS_TAC[DIV_GT0,DECIDE ``0<2``,ONE_LT_dimword,Abbr`b`,LESS_EQ,TWO]) >>
               DECIDE_TAC)>>
       DECIDE_TAC)>>
  strip_tac >>
  qpat_x_assum `~x` (fn x => ASSUME_TAC(MP ((fn (x,y) => x)(EQ_IMP_RULE (Q.SPECL [`V`,`U`] NOT_LESS_EQUAL))) x)) >>
  `LENGTH ((REVERSE us) ++ [u2]) = SUC(LENGTH us)` by lrw[] >>
  `U = mw2n (REVERSE us) + dimword(:'a) ** LENGTH us * w2n u2 + dimword(:'a) ** (LENGTH(REVERSE us ++ [u2])) * w2n u1` by full_simp_tac (srw_ss())[Abbr`U`,LENGTH_REVERSE,GSYM ADD1,mw2n_msf,dimwords_dimword] >>
  `U = mw2n (REVERSE us) + dimword(:'a) ** LENGTH us * w2n u2 + dimword(:'a) ** (LENGTH us) * dimword(:'a) * w2n u1` by full_simp_tac (srw_ss())[EXP,MULT_COMM] >>
  qpat_x_assum `U = xxx` (fn x => ASSUME_TAC(RW[GSYM MULT_ASSOC,GSYM ADD_ASSOC,GSYM LEFT_ADD_DISTRIB] x)) >>
  `V = mw2n (REVERSE vs) + dimword(:'a) ** LENGTH vs * w2n v1` by full_simp_tac (srw_ss())[mw2n_msf,dimwords_dimword] >>
  `V < dimword(:'a) ** LENGTH vs * SUC (w2n v1)` by METIS_TAC[mw2n_lt,LENGTH_REVERSE,LESS_MONO_ADD,MULT,ADD_COMM,MULT_COMM,dimwords_dimword] >>
  `U < dimword(:'a) ** SUC(LENGTH us)` by METIS_TAC[mw2n_lt,LESS_TRANS,LENGTH_REVERSE,LENGTH,dimwords_dimword]>>
  `w2n u2 + dimword(:'a) * w2n u1 <= w2n v1` by METIS_TAC[ADD_COMM,LESS_EQ_ADD,LESS_EQ_LESS_TRANS,LESS_TRANS,LT_MULT_LCANCEL,DECIDE ``a < SUC b ==> (a <= b)``] >>
  `MIN a b <= a` by lrw[] >>
  `q' <= (w2n u2 +  dimword(:'a)*w2n u1) DIV w2n v1` by full_simp_tac (srw_ss())[ADD_COMM,MULT_COMM,Abbr`q'`]>>
  `0 < w2n v1` by METIS_TAC[DIV_GT0,DECIDE ``0<2``,ONE_LT_dimword,LESS_EQ,TWO,ONE,LESS_EQ_TRANS]  >>
  `(w2n u2 +  dimword(:'a)*w2n u1) DIV w2n v1 <= 1` by (Cases_on `w2n u2 + dimword(:'a)*w2n u1 = w2n v1` THEN1 (RW_TAC arith_ss[]) >>
  `(w2n u2 + dimword(:'a) * w2n u1) < w2n v1` by RW_TAC arith_ss[] >> METIS_TAC[LESS_DIV_EQ_ZERO, DECIDE ``0<=1``]) >>
  lrw[]);

val mw_div_test_lemma1 = Q.store_thm( "mw_div_test_lemma1",
`!q u1 u2 u3 v1 v2. w2n (mw_div_test q u1 u2 u3 v1 v2) <= w2n q`,
    HO_MATCH_MP_TAC mw_div_test_ind >> REPEAT strip_tac >>
    srw_tac[][Once mw_div_test_def] >>
    `w2n q2 <= w2n q` by
    METIS_TAC[Abbr`q2`,w2n_n2w,ZERO_LT_dimword,MOD_LESS_EQ,LESS_EQ_TRANS,DECIDE ``x - 1 <=x``] >>
    Cases_on `mw_cmp [u2; u1] (FST (mw_add [FST s; SND s] [0w; 1w] F)) = SOME T`
           >> full_simp_tac (srw_ss())[] >> METIS_TAC[LESS_EQ_TRANS])

val mw_div_test_lemma2 = Q.store_thm( "mw_div_test_lemma2",
`!(us:'a word list) (vs:'a word list).
  !q u1 u2 u3 v1 v2.
   (0 < w2n v1) /\ (LENGTH us = LENGTH vs) /\
   (mw2n (REVERSE (u1::u2::u3::us)) DIV mw2n (REVERSE (v1::v2::vs)) < dimword(:'a)) /\
   (mw2n (REVERSE (u1::u2::u3::us)) DIV mw2n (REVERSE (v1::v2::vs)) <= w2n q) ==>
   (mw2n (REVERSE (u1::u2::u3::us)) DIV mw2n (REVERSE (v1::v2::vs))
    <= w2n (mw_div_test q u1 u2 u3 v1 v2))`,

    GEN_TAC >> GEN_TAC >>
    HO_MATCH_MP_TAC mw_div_test_ind >>
    REPEAT strip_tac >>
    Cases_on `(mw_cmp [u3; u2; u1] (mw_mul_by_single q [v2; v1]) = SOME T)`
    THEN1( Q.PAT_ABBREV_TAC `u = u1::u2::u3::us` >>
           Q.PAT_ABBREV_TAC` v = v1::v2::vs` >>
           srw_tac[][Once mw_div_test_def] >>
           qsuff_tac `mw2n (REVERSE (u:'a word list)) DIV mw2n (REVERSE (v:'a word list)) <= w2n (n2w (w2n (q:'a word) - 1):'a word)`
           THEN1( strip_tac >>
                  Cases_on `mw_cmp [u2; u1] (FST (mw_add [FST s; SND s] [0w; 1w] F)) = SOME T` >>
                  METIS_TAC[Abbr`q2`]) >>
           qpat_x_assum `!q'. xxx` (K ALL_TAC) >>
           qsuff_tac `w2n u1 * dimword (:'a) * dimword (:'a) + w2n u2 * dimword (:'a) + w2n u3 < w2n q * (w2n v1 * dimword (:'a) + w2n v2)`
           THEN1( strip_tac >>
                  Cases_on `mw2n (REVERSE u) DIV mw2n (REVERSE v) = 0` THEN1 DECIDE_TAC >>
                  `0 < w2n q` by DECIDE_TAC >>
                  `w2n (n2w (w2n (q:'a word) - 1):'a word) = w2n q - 1` by METIS_TAC[w2n_n2w,LESS_MOD,DECIDE ``x - 1 <= x``,LESS_EQ_LESS_TRANS,w2n_lt] >>
                  POP_ASSUM (fn x => REWRITE_TAC[x]) >>
                  markerLib.UNABBREV_TAC "v" >>
                  srw_tac[][mw2n_msf,EXP, GSYM ADD1,dimwords_dimword] >>
                  `0 < w2n v1 * dimword(:'a) + w2n v2`
                   by METIS_TAC[ZERO_LT_dimword,LE_MULT_CANCEL_LBARE,LESS_EQ_ADD,LESS_EQ_TRANS,LESS_LESS_EQ_TRANS] >>
                   `0 < dimword(:'a) ** (LENGTH vs)` by  METIS_TAC[ZERO_LT_dimword,ZERO_LT_EXP]  >>
                   Q.PAT_ABBREV_TAC `U = mw2n (REVERSE u)` >>
                   qsuff_tac `U DIV ((w2n v1 * dimword(:'a) + w2n v2) * dimword(:'a)**(LENGTH vs)) <= w2n q - 1`
                   THEN1( Q.PAT_ABBREV_TAC`X = (w2n v1 * dimword(:'a) + w2n v2) * dimword(:'a) ** (LENGTH vs)` >>
                          Q.PAT_ABBREV_TAC`V = mw2n (REVERSE vs) + dimword (:'a) ** LENGTH vs * w2n v2 + dimword (:'a) * dimword (:'a) ** LENGTH vs * w2n v1` >>
                          strip_tac >>
                          `0 < X` by METIS_TAC[Abbr `X`,ZERO_LESS_MULT]>>
                          `X <= V` by METIS_TAC[LESS_EQ_ADD,LESS_EQ_TRANS,DECIDE ``vs + l*v2 + b*l*v1 = (v1*b + v2)*l + vs``] >>
                          METIS_TAC[DIV_thm1,LESS_EQ_TRANS]) >>
                   Q.PAT_ABBREV_TAC`X1 = w2n v1 * dimword(:'a) + w2n v2` >>
                   Q.PAT_ABBREV_TAC`X2 = dimword(:'a) ** LENGTH vs` >>
                   `U DIV (X1 * X2) = U DIV X2 DIV X1` by METIS_TAC[MULT_COMM,DIV_DIV_DIV_MULT] >>
                   qpat_x_assum `U DIV xxx = yyy` (fn x => REWRITE_TAC[x]) >>
                   srw_tac[][Abbr`U`,Abbr`u`,mw2n_msf,dimwords_dimword,EXP, GSYM ADD1] >>
                   REWRITE_TAC[DECIDE ``u + x2 * u3 + b * x2 * u2 + b * (b * x2) * u1 = (u3 + u2*b + u1*b*b)*x2 + u``] >>
                   Q.PAT_ABBREV_TAC`A = (w2n u3 + w2n u2 * dimword (:'a) + w2n u1 * dimword (:'a) * dimword (:'a))` >>
                   Q.PAT_ABBREV_TAC`B = mw2n (REVERSE us)` >>
                   `(A * X2 + B) DIV X2 = A` by METIS_TAC[DIV_MULT,Abbr`X2`,Abbr`B`,mw2n_lt,dimwords_dimword,LENGTH_REVERSE] >>
                   qpat_x_assum `xx DIV X2 = A` (fn x => REWRITE_TAC[x]) >>
                   `A < w2n q * X1` by METIS_TAC[ADD_COMM,ADD_ASSOC] >>
                   `A DIV X1 < w2n q` by METIS_TAC[DIV_thm2] >>
                   Cases_on `w2n q` THEN1 full_simp_tac (srw_ss())[] >>
                   METIS_TAC[SUC_SUB1,LESS_EQ,LESS_EQ_MONO]) >>
            REWRITE_TAC[DECIDE ``a1 * d * d + a2 * d + a3 = a3 + d * (a2 + ( d * a1))``,
                        DECIDE ``w * (b1 * d + b2) = w *( b2 + d * b1)``] >>
            `(w2n u1 = mw2n [u1]) /\ (w2n v1 = mw2n [v1])` by lrw[mw2n_def] >>
            POP_ASSUM (fn x => REWRITE_TAC[x]) >> POP_ASSUM (fn x => REWRITE_TAC[x]) >>
            REWRITE_TAC[SPEC_ALL (GSYM (CONJUNCT2 mw2n_def)),GSYM (CONJUNCT1 (SPEC_ALL mw_mul_by_single_lemma))] >>
            `LENGTH [u3;u2;u1] = LENGTH (mw_mul_by_single q [v2;v1])` by lrw[mw_mul_by_single_lemma] >>
            FULL_SIMP_TAC std_ss [mw_cmp_thm]) >>
full_simp_tac (srw_ss())[Once mw_div_test_def] )

val q_thm = Q.store_thm( "q_thm",
`!(u1:'a word) u2 us (v1:'a word) vs.
  (LENGTH us = LENGTH vs) /\ (0 < w2n v1) /\
  (mw2n (REVERSE (u1::u2::us)) DIV mw2n (REVERSE (v1::vs)) < dimword(:'a)) ==>
  w2n u1 * dimword(:'a) + w2n u2 < dimword(:'a) * (1 + w2n v1)`,

    REPEAT GEN_TAC >>
    Q.PAT_ABBREV_TAC`U = mw2n (REVERSE (u1::u2::us))` >>
    Q.PAT_ABBREV_TAC`V = mw2n (REVERSE (v1::vs))` >>
    strip_tac >>
    EQT_M_R_S_i `dimword(:'a) ** LENGTH (us:'a word list)` >>
    `0 < V` by (full_simp_tac (srw_ss())[Abbr`V`,mw2n_msf,dimwords_dimword,Once ADD_COMM,Once MULT_COMM]
            >> METIS_TAC[ZERO_LT_dimword,ZERO_LT_EXP,LESS_EQ_ADD, LE_MULT_CANCEL_LBARE,
               LESS_LESS_EQ_TRANS]) >>
    `U < dimword(:'a) * V` by METIS_TAC[DIV_LT_X] >>
    MATCH_MP_TAC LESS_EQ_LESS_TRANS >> EXISTS_TAC ``(U:num)`` >> strip_tac THEN1(
    lrw[Abbr`U`,mw2n_msf,dimwords_dimword] >>
    REWRITE_TAC[ DECIDE  ``(w2 + d * w1) * d ** l = w1 * (d * d ** l) + w2 * d ** l``,GSYM EXP, ADD1] >>
    METIS_TAC[LESS_EQ_TRANS,LESS_EQ_ADD,ADD_COMM]) >>
    MATCH_MP_TAC LESS_LESS_EQ_TRANS >> EXISTS_TAC ``dimword(:'a) * V`` >> strip_tac THEN1 DECIDE_TAC >>
    ASM_REWRITE_TAC[] >>
    qsuff_tac `V <= (1 + w2n v1) * dimword(:'a) ** LENGTH vs` THEN1 (
    strip_tac >> METIS_TAC[MULT_COMM,LESS_MONO_MULT,MULT_ASSOC] ) >>
    lrw[Abbr`V`,mw2n_msf,dimwords_dimword] >> REWRITE_TAC[RIGHT_ADD_DISTRIB,MULT_LEFT_1] >>
    METIS_TAC[LENGTH_REVERSE,ADD_COMM,LESS_EQ_MONO_ADD_EQ,mw2n_lt,dimwords_dimword,LESS_IMP_LESS_OR_EQ] );

val mw_div_test_thm = Q.store_thm( "mw_div_test_thm",
`!(u1:'a word) u2 u3 us (v1:'a word) v2 vs.
  (LENGTH us = LENGTH vs) /\ (dimword(:'a) DIV 2 <= w2n v1) /\
  (mw2n (REVERSE (u1::u2::u3::us)) DIV (mw2n (REVERSE (v1::v2::vs))) < dimword(:'a))  ==>
  (let q = if w2n u1 < w2n v1 then FST (single_div u1 u2 v1) else (n2w (dimword(:'a) - 1):'a word) in
  w2n (mw_div_test q u1 u2 u3 v1 v2) < dimword(:'a) /\ (
  (w2n (mw_div_test q u1 u2 u3 v1 v2) =
    mw2n (REVERSE (u1::u2::u3::us)) DIV mw2n (REVERSE (v1::v2::vs))) \/
   (w2n (mw_div_test q u1 u2 u3 v1 v2) =
    SUC (mw2n (REVERSE (u1::u2::u3::us)) DIV mw2n (REVERSE (v1::v2::vs))))))`,
    REPEAT GEN_TAC >>
    Q.PAT_ABBREV_TAC`U = mw2n (REVERSE (u1::u2::u3::us))` >>
    Q.PAT_ABBREV_TAC`V = mw2n (REVERSE (v1::v2::vs))` >>
    Q.PAT_ABBREV_TAC`Q =  U DIV V` >>
    strip_tac >>
    Q.PAT_ABBREV_TAC `q = if w2n u1 < w2n v1 then FST (single_div u1 u2 v1) else n2w (dimword (:'a) - 1)` >>
    srw_tac[][] THEN1 METIS_TAC[w2n_lt] >>
    `LENGTH (u3::us) = LENGTH (v2::vs)` by lrw[] >>
    `0 < w2n v1` by METIS_TAC[ONE_LT_dimword,DECIDE ``0<2 /\ ((1<x)==>(2 <= x))``,DIV_GT0,LESS_LESS_EQ_TRANS] >>
    `0 < V` by (full_simp_tac (srw_ss())[Abbr`V`,mw2n_msf,dimwords_dimword,Once ADD_COMM,Once MULT_COMM]
            >> METIS_TAC[ZERO_LT_dimword,ZERO_LT_EXP,LESS_EQ_ADD, LE_MULT_CANCEL_LBARE,
               LESS_LESS_EQ_TRANS]) >>
    `w2n q = MIN ((w2n u1 * dimword (:'a) + w2n u2) DIV w2n v1) (dimword (:'a) - 1)` by ALL_TAC
    THEN1( markerLib.UNABBREV_TAC "q" >>
           srw_tac[][single_div_def]
           THEN1( IMP_RES_TAC single_div_lemma1 >>
                  POP_ASSUM (fn x => ASSUME_TAC (Q.SPECL [`u2:'a word`] x)) >>
                  FULL_SIMP_TAC arith_ss[] >>
                  `!a b. (a <= b) ==> (a = MIN a b)` by lrw[MIN_DEF] >>
                  METIS_TAC[SUB_LESS_OR]) >>
           `!a b. (a <= b) ==> (a = MIN b a)` by lrw[MIN_DEF,MIN_COMM] >>
           POP_ASSUM(fn x => MATCH_MP_TAC x) >>
           `!a b. a * w2n v1 <= b ==> (a <= b DIV w2n v1)` by METIS_TAC[X_LE_DIV] >>
           POP_ASSUM(fn x => MATCH_MP_TAC x) >>
           REWRITE_TAC[RIGHT_SUB_DISTRIB] >>
           METIS_TAC[NOT_LESS,MULT_COMM,LESS_MONO_MULT,SUB_LESS_EQ,LESS_EQ_ADD,LESS_EQ_TRANS]) >>
    markerLib.RM_ABBREV_TAC "q" >>
    `dimword(:'a) - 1 < dimword(:'a)` by (Cases_on `dimword(:'a)` >> full_simp_tac (srw_ss())[ZERO_LT_dimword]) >>
    `w2n q <= dimword(:'a)-1` by METIS_TAC[w2n_lt,SUB_LESS_OR]  >>
    `w2n q>=Q` by METIS_TAC[Abbr`Q`,mw_div_range1,Abbr `U`, Abbr`V`] >>
    qpat_x_assum `w2n q >= Q` (fn x => ASSUME_TAC(METIS_PROVE [x,GREATER_EQ] ``Q <= w2n q``)) >>
    `Q <= w2n (mw_div_test q u1 u2 u3 v1 v2)` by METIS_TAC[mw_div_test_lemma2] >>
    `w2n q <= Q + 2` by METIS_TAC[Abbr`Q`,mw_div_range2,Abbr `U`, Abbr`V`] >>
    REV (Cases_on `w2n q = Q + 2`) THEN1
      (`w2n q <= SUC Q` by DECIDE_TAC >>
       Q.PAT_ABBREV_TAC`test = w2n (mw_div_test q u1 u2 u3 v1 v2)` >>
       `test <> dimword(:'a)` by METIS_TAC[w2n_lt,prim_recTheory.LESS_NOT_EQ] >>
       `test <= w2n q` by METIS_TAC[mw_div_test_lemma1] >>
       DECIDE_TAC) >>
    REV (`mw_cmp [u3; u2; u1] (mw_mul_by_single q [v2; v1]) = SOME T` by ALL_TAC)
    THEN1 (Q.PAT_ABBREV_TAC`test = w2n (mw_div_test q u1 u2 u3 v1 v2)` >>
           `test <= w2n q - 1` by ALL_TAC
           THEN1( markerLib.UNABBREV_TAC "test" >>
                  REPEAT (qpat_x_assum `w2n q = xxx` (K ALL_TAC)) >>
                  srw_tac[][Once mw_div_test_def] >>
                  `w2n q2 = w2n q - 1` by (markerLib.UNABBREV_TAC "q2" >> lrw[]) >>
                  Cases_on `mw_cmp [u2; u1] (FST (mw_add [FST s; SND s] [0w; 1w] F)) = SOME T` >>
                  srw_tac[][] THEN1 METIS_TAC[LESS_EQ_REFL,LESS_EQ_TRANS,mw_div_test_lemma1] >>
                  DECIDE_TAC) >>
           DECIDE_TAC) >>
    REV (`w2n u1 * dimword(:'a) * dimword(:'a) + w2n u2 * dimword(:'a) + w2n u3 < w2n q * (w2n v1 * dimword(:'a) + w2n v2)` by ALL_TAC)
    THEN1
      (qsuff_tac `mw2n [u3;u2;u1] < mw2n (mw_mul_by_single q [v2;v1])`
       THEN1( `LENGTH [u3;u2;u1] = LENGTH (mw_mul_by_single q [v2;v1])` by METIS_TAC[mw_mul_by_single_lemma,LENGTH,ADD1] >>
       FULL_SIMP_TAC std_ss [mw_cmp_thm,prim_recTheory.LESS_NOT_EQ]) >>
       REPEAT (qpat_x_assum `w2n q = xxx` (K ALL_TAC)) >>
       FULL_SIMP_TAC arith_ss[mw2n_def,mw_mul_by_single_lemma,LEFT_ADD_DISTRIB]) >>
    Q.PAT_ABBREV_TAC` b = dimword(:'a)` >>
    Q.PAT_ABBREV_TAC`V1 = w2n v1` >>
    Q.PAT_ABBREV_TAC`V2 = w2n v2` >>
    Q.PAT_ABBREV_TAC`U1 = w2n u1` >>
    Q.PAT_ABBREV_TAC`U2 = w2n u2` >>
    Q.PAT_ABBREV_TAC`U3 = w2n u3` >>
    EQT_M_R_S_i `b**(LENGTH (vs:'a word list))` >>
    `w2n q * mw2n (REVERSE vs) <= mw2n (REVERSE (us:'a word list)) + mw2n (REVERSE (v1::v2::(vs:'a word list)))` by ALL_TAC
    THEN1( MATCH_MP_TAC (GEN_ALL (Q.SPECL [`a1*a2`,`a4`,`a5+a4`] LESS_EQ_TRANS)) >>
           REV strip_tac THEN1 METIS_TAC[LESS_EQ_ADD,ADD_COMM] >>
           MATCH_MP_TAC LESS_EQ_TRANS >>
           EXISTS_TAC ``(b:num) * b ** LENGTH (vs:'a word list)`` >>
           strip_tac THEN1
             (MATCH_MP_TAC LESS_MONO_MULT2 \\ STRIP_TAC
              THEN1 (FULL_SIMP_TAC std_ss [])
              \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
              \\ Q.UNABBREV_TAC `b`
              \\ FULL_SIMP_TAC std_ss [dimword_def,GSYM EXP_EXP_MULT]
              \\ ONCE_REWRITE_TAC [MULT_COMM]
              \\ FULL_SIMP_TAC std_ss [GSYM dimwords_def]
              \\ MATCH_MP_TAC (DECIDE ``n < m ==> n <= m:num``)
              \\ SIMP_TAC std_ss [mw2n_lt]) >>
            markerLib.UNABBREV_TAC "V" >> lrw[mw2n_msf,dimwords_dimword,GSYM ADD1,GSYM EXP]>>
            ONCE_REWRITE_TAC[DECIDE``a + (b + c) = b + (a + c):num``] >>
            Cases_on `V1` THEN1 full_simp_tac (srw_ss())[] >>
            Q.PAT_ABBREV_TAC`A = b ** SUC(LENGTH vs)`>>
            Q.PAT_ABBREV_TAC`B = mw2n (REVERSE vs) + V2 * b ** LENGTH vs`>>
            METIS_TAC[MULT,MULT_COMM,ADD_COMM,ADD_ASSOC,LESS_EQ_ADD])>>
    EQT_A_S_R_2 (`mw2n (REVERSE (us:'a word list)) + mw2n (REVERSE (v1::v2::(vs:'a word list)))`,`w2n (q:'a word) * mw2n (REVERSE (vs:'a word list))`) >>
    REWRITE_TAC [DECIDE ``(U1 * b * b + U2 * b + U3) * b**y + (u + V:num) =
                    u + b**y * U3 + b * b**y * U2 + b * b * b**y * U1 + V``] >>
    markerLib.UNABBREV_TAC "b" >>
    markerLib.UNABBREV_TAC "U3" >> markerLib.UNABBREV_TAC "U2" >> markerLib.UNABBREV_TAC "U1" >>
    qpat_x_assum `LENGTH us = xxx` (fn x => (ASSUME_TAC x \\ REWRITE_TAC[GSYM x])) >>
    REWRITE_TAC[DECIDE ``b*b*b**c = (b:num)*(b*b**c)``,GSYM EXP, Once
    (METIS_PROVE [ADD1,LENGTH_APPEND,LENGTH_REVERSE,EVAL ``LENGTH [x]``]``SUC(LENGTH us) = LENGTH ((REVERSE us)++[u3])``),
    Once (METIS_PROVE [ADD1,LENGTH_APPEND,LENGTH_REVERSE,EVAL ``LENGTH [x]``] ``SUC(SUC(LENGTH us)) = LENGTH (((REVERSE us)++[u3])++[u2])``)] >>
    REWRITE_TAC[Once (GSYM LENGTH_REVERSE),GSYM mw2n_msf,GSYM dimwords_dimword,METIS_PROVE [REVERSE,SNOC_APPEND] ``(REVERSE xs) ++ [x] = REVERSE (x::xs)``] >>
    ASM_REWRITE_TAC[] >>
    REWRITE_TAC[dimwords_dimword]>>
    REWRITE_TAC[DECIDE``(A:num) * (V1 * b + V2) * b ** c + A * vs = A * (vs + b ** c * V2 + b * b ** c * V1)``,GSYM EXP,
                  Once (METIS_PROVE [ADD1,LENGTH_APPEND,LENGTH_REVERSE,EVAL ``LENGTH [x]``]``SUC(LENGTH vs) = LENGTH ((REVERSE vs)++[v2])``)] >>
    markerLib.UNABBREV_TAC"V2" >> markerLib.UNABBREV_TAC "V1" >>
    REWRITE_TAC[Once (GSYM LENGTH_REVERSE),GSYM mw2n_msf,GSYM dimwords_dimword,METIS_PROVE [REVERSE,SNOC_APPEND] ``(REVERSE xs) ++ [x] = REVERSE (x::xs)``] >>
    REWRITE_TAC[RIGHT_ADD_DISTRIB,DECIDE ``2 = 1+1:num``,MULT_LEFT_1,ADD_ASSOC] >>
    MATCH_MP_TAC LESS_MONO_ADD >>
    METIS_TAC[Abbr`Q`,Abbr`U`,Abbr`V`,DIV_thm4_bis,ADD_COMM,MULT_COMM]);

val mw_div_loop_LENGTH = Q.store_thm( "mw_div_loop_LENGTH",
`!(zs:'a word list) (ys:'a word list).
  dimword(:'a) DIV 2 <= w2n (HD ys) /\
  LENGTH ys < LENGTH zs /\
  1 < LENGTH ys  ==>
  (LENGTH (mw_div_loop zs ys) = LENGTH zs)`,

HO_MATCH_MP_TAC mw_div_loop_ind >>
REPEAT strip_tac >>
srw_tac[][Once mw_div_loop_def] >>
Cases_on `mw_cmp (REVERSE us) q2ys = SOME T` >>
srw_tac[][]
THEN1 (qpat_x_assum `! us q q2. xxx` (K ALL_TAC) >>
       qpat_x_assum `! us. xxx` (fn x => ASSUME_TAC (Q.SPECL [`us`,`q`,`q2`,`q2ys`,`q3`,`q3ys`,`zs2'`] x)) >>
       `LENGTH zs = SUC (LENGTH zs2')` by ALL_TAC
       THEN1(`LENGTH q3ys = LENGTH us` by METIS_TAC[Abbr`us`,Abbr`q3ys`,mw_mul_by_single_lemma,ADD1,LENGTH_TAKE,LESS_EQ,LENGTH_REVERSE] >>
             markerLib.UNABBREV_TAC "zs2'" >>
             REWRITE_TAC[LENGTH_APPEND,LENGTH_REVERSE,LENGTH_DROP] >>
             Q.PAT_ABBREV_TAC `X = (FST (mw_sub (REVERSE us) q3ys T))` >>
             `0 < LENGTH us /\ (LENGTH us = SUC(LENGTH ys))` by METIS_TAC[LENGTH_TAKE,LESS_EQ,DECIDE ``0 < SUC x``] >>
             `X <> [] /\ (LENGTH X = SUC(LENGTH ys))` by METIS_TAC[mw_sub_lemma,PAIR,LENGTH_REVERSE,NOT_NIL_EQ_LENGTH_NOT_0] >>
             srw_tac[][rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
             RW_TAC arith_ss[]) >>
       Cases_on `LENGTH ys < LENGTH zs2'` THEN1 METIS_TAC[] >>
       srw_tac[][Once mw_div_loop_def]) >>
qpat_x_assum `! us. xxx` (fn x => ASSUME_TAC (Q.SPECL [`us`,`q`,`q2`,`q2ys`,`zs2`] x)) >>
qpat_x_assum `! us q q2. xxx` (K ALL_TAC) >>
`LENGTH zs = SUC (LENGTH zs2)` by ALL_TAC
THEN1 (`LENGTH q2ys = LENGTH us` by METIS_TAC[Abbr`us`,Abbr`q2ys`,mw_mul_by_single_lemma,ADD1,LENGTH_TAKE,LESS_EQ,LENGTH_REVERSE] >>
       markerLib.UNABBREV_TAC "zs2" >>
       REWRITE_TAC[LENGTH_APPEND,LENGTH_REVERSE,LENGTH_DROP] >>
       Q.PAT_ABBREV_TAC `X = (FST (mw_sub (REVERSE us) q2ys T))` >>
       `0 < LENGTH us /\ (LENGTH us = SUC(LENGTH ys))` by METIS_TAC[LENGTH_TAKE,LESS_EQ,DECIDE ``0 < SUC x``] >>
       `X <> [] /\ (LENGTH X = SUC(LENGTH ys))` by METIS_TAC[mw_sub_lemma,PAIR,LENGTH_REVERSE,NOT_NIL_EQ_LENGTH_NOT_0] >>
       srw_tac[][rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
       RW_TAC arith_ss[]) >>
Cases_on `LENGTH ys < LENGTH zs2` THEN1 METIS_TAC[] >>
srw_tac[][Once mw_div_loop_def])

val tac_div_loop_1 =
      `mw2n (REVERSE (TAKE (SUC (LENGTH ys)) zs2)) DIV mw2n (REVERSE ys) < dimword (:'a)` by ALL_TAC
      THEN1( `SUC (LENGTH ys) < LENGTH zs` by DECIDE_TAC >>
              markerLib.UNABBREV_TAC "zs2" >>
              `LENGTH (FRONT w) = LENGTH ys` by METIS_TAC[prim_recTheory.PRE,LENGTH_BUTLAST] >>
              `LENGTH (REVERSE (FRONT w)) < SUC (LENGTH ys)` by METIS_TAC[LENGTH_REVERSE,DECIDE ``x < SUC x``] >>
              srw_tac[][TAKE_APPEND2,REVERSE_APPEND,SUC_SUB] >>
              `LENGTH (TAKE 1 (DROP (SUC (LENGTH ys)) zs)) = 1` by METIS_TAC[LENGTH_TAKE,LENGTH_DROP,LESS_EQ,SUB_LESS_0,ONE] >>
              srw_tac[][mw2n_APPEND,dimwords_dimword] >>
              `!a b. (a < b * mw2n (REVERSE ys) ==> a DIV mw2n (REVERSE ys) < b)` by METIS_TAC[DIV_LT_X] >>
              POP_ASSUM (fn x => MATCH_MP_TAC x) >>
              MATCH_MP_TAC LESS_LESS_EQ_TRANS >> EXISTS_TAC ``dimword(:'a) * SUC (mw2n (REVERSE (us:'a word list)) - mw2n (q3ys:'a word list))`` >>
              strip_tac
              THEN1( REWRITE_TAC[METIS_PROVE [MULT,MULT_COMM,ADD_COMM] ``a * SUC b = a + a * b``] >>
                     `!(x:num). x ** 1 = x` by
                     (GEN_TAC >> REWRITE_TAC[ONE,Q.SPECL [`x`,`0`] (CONJUNCT2 EXP)] >>
                     RW_TAC arith_ss[]) >>
                     MATCH_MP_TAC LESS_MONO_ADD >>
                     METIS_TAC[LESS_MONO_ADD,mw2n_lt,dimwords_dimword,LENGTH_REVERSE]) >>
              markerLib.UNABBREV_TAC "q3ys" >>
              ASM_REWRITE_TAC[mw_mul_by_single_lemma] >>
              METIS_TAC[LESS_MONO_MULT,MULT_COMM,DIV_thm4,LESS_EQ]) >>
      `mw2n (REVERSE (BUTLASTN (LENGTH ys) (mw_div_loop zs2 ys))) *
      mw2n (REVERSE ys) + mw2n (REVERSE (LASTN (LENGTH ys) (mw_div_loop zs2 ys))) =
      mw2n (REVERSE zs2)` by METIS_TAC[] >>
      qpat_x_assum ` xx /\ (us = us) /\ yyy ==> zz` (K ALL_TAC) >>
      `LENGTH ys <= LENGTH (mw_div_loop zs2 ys) /\ (LENGTH (mw_div_loop zs2 ys) = LENGTH zs2)` by METIS_TAC[mw_div_loop_LENGTH,LESS_IMP_LESS_OR_EQ] >>
      srw_tac[][rich_listTheory.LASTN_CONS,rich_listTheory.BUTLASTN_CONS,mw2n_msf,dimwords_dimword,rich_listTheory.LENGTH_BUTLASTN] >>
      REWRITE_TAC[DECIDE ``(a + b)* c + d = a*c + d + b*c``] >>
      qpat_x_assum `xxx = mw2n (REVERSE zs2)` (fn x => REWRITE_TAC[x]) >>
      markerLib.UNABBREV_TAC "zs2" >> REWRITE_TAC[REVERSE_APPEND,REVERSE_REVERSE,mw2n_APPEND] >>
      qpat_x_assum `mw2n (FRONT xx) = mw2n xx` (fn x => REWRITE_TAC[x]) >>
      REWRITE_TAC[LENGTH_REVERSE,LENGTH_APPEND,LENGTH_DROP] >>
      full_simp_tac (srw_ss())[rich_listTheory.LENGTH_BUTLAST] >>
      markerLib.UNABBREV_TAC "q3ys" >>
      full_simp_tac (srw_ss())[mw_mul_by_single_lemma] >>
      `zs = us ++ (DROP (SUC(LENGTH ys)) zs)` by METIS_TAC[Abbr`us`,TAKE_DROP] >>
      POP_ASSUM (fn x => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [x]))) >>
      REWRITE_TAC[REVERSE_APPEND,mw2n_APPEND,dimwords_dimword,LENGTH_DROP,LENGTH_REVERSE] >>
      REWRITE_TAC[DECIDE ``a + b*c + b*d*e = a + b*(c +d*e)``] >>
      METIS_TAC[DIV_thm3,SUB_ADD];

val tac_div_loop_2 =
        srw_tac[][Once mw_div_loop_def] >>
        srw_tac[][Once mw_div_loop_def] >> POP_ASSUM (K ALL_TAC) >>
        `LENGTH zs2 = LENGTH ys` by DECIDE_TAC   >>
        `LENGTH ys <= LENGTH (q3::zs2)` by METIS_TAC[LENGTH,DECIDE ``n <= SUC n``] >>
        srw_tac[][rich_listTheory.BUTLASTN_CONS,rich_listTheory.LASTN_CONS,mw2n_msf,dimwords_dimword] >>
        `(BUTLASTN (LENGTH ys) zs2 = []) /\
         (LASTN (LENGTH ys) zs2 = zs2)` by METIS_TAC[rich_listTheory.BUTLASTN_LENGTH_NIL,rich_listTheory.LASTN_LENGTH_ID] >>
        POP_ASSUM (fn x => REWRITE_TAC[x]) >>    POP_ASSUM (fn x => REWRITE_TAC[x]) >>
        RW_TAC arith_ss[LENGTH,REVERSE,mw2n_def] >>
        markerLib.UNABBREV_TAC "zs2">>
        ASM_REWRITE_TAC[REVERSE_REVERSE,REVERSE_APPEND,mw2n_APPEND,dimwords_dimword]>>
        markerLib.UNABBREV_TAC "q3ys" >> srw_tac[][mw_mul_by_single_lemma] >>
        RW_TAC arith_ss[] >>
        ONCE_REWRITE_TAC[GSYM ADD_ASSOC] >>
        Q.PAT_ABBREV_TAC `x = mw2n (REVERSE ys) * (mw2n (REVERSE us) DIV mw2n (REVERSE ys))` >>
        `mw2n (REVERSE us) - x + x = mw2n (REVERSE us)` by METIS_TAC[MULT_COMM,DIV_thm3,SUB_ADD,Abbr`x`] >>
        POP_ASSUM (fn x => REWRITE_TAC[x]) >>
        markerLib.UNABBREV_TAC "us" >>
        `SUC(LENGTH ys) = LENGTH zs` by DECIDE_TAC >> POP_ASSUM (fn x => REWRITE_TAC[x]) >>
        srw_tac[][rich_listTheory.BUTFIRSTN_LENGTH_NIL,listTheory.TAKE_LENGTH_ID,mw2n_def];

val tac_div_loop_test =
       Cases_on `us` THEN1 full_simp_tac (srw_ss())[] >> Cases_on `t` THEN1 full_simp_tac (srw_ss())[] >> Cases_on `t'` THEN1 full_simp_tac (srw_ss())[] >>
       Cases_on `ys` THEN1 full_simp_tac (srw_ss())[] >> Cases_on `t'` THEN1 full_simp_tac (srw_ss())[] >>
       FULL_SIMP_TAC std_ss[HD,TL,LENGTH] >>
       METIS_TAC[mw_div_test_thm];

val mw_div_loop_thm = Q.store_thm( "mw_div_loop_thm",
`!(zs:'a word list) (ys:'a word list).
  dimword(:'a) DIV 2 <= w2n (HD ys) /\
  LENGTH ys < LENGTH zs /\ 1 < LENGTH ys /\
  ((mw2n (REVERSE (TAKE (SUC (LENGTH ys)) zs)) DIV mw2n (REVERSE ys)) < dimword(:'a) ) ==>
  (let rslt = mw_div_loop zs ys in
   mw2n (REVERSE( BUTLASTN (LENGTH ys) rslt)) * mw2n (REVERSE ys) + mw2n (REVERSE (LASTN (LENGTH ys) rslt)) =
   mw2n (REVERSE zs))`,

  HO_MATCH_MP_TAC mw_div_loop_ind >> REPEAT strip_tac >>
  srw_tac[][Once mw_div_loop_def] >>
  markerLib.UNABBREV_TAC "rslt" >>
  Cases_on `mw_cmp (REVERSE us) q2ys = SOME T` >>
  srw_tac[][]

THENL[qpat_x_assum `!us. xxx` (K ALL_TAC) >>
      qpat_x_assum `!us. xxx` (fn x => ASSUME_TAC (Q.SPECL [`us`,`q`,`q2`,`q2ys`,`q3`,`q3ys`,`zs2'`] x)),
      qpat_x_assum `!us. xxx` (fn x => ASSUME_TAC (Q.SPECL [`us`,`q`,`q2`,`q2ys`,`zs2`] x)) >>
      qpat_x_assum `!us. xxx` (K ALL_TAC)]
THENL[ALL_TAC,markerLib.UNABBREV_TAC "q3" >> markerLib.UNABBREV_TAC "q2" >>
      Q.PAT_ABBREV_TAC `q3 = mw_div_test q (HD us) (HD (TL us)) (HD (TL (TL us))) (HD ys) (HD (TL ys))`] >>
markerLib.UNABBREV_TAC "zs2" >>
markerLib.UNABBREV_TAC "zs2'" >>
markerLib.UNABBREV_TAC "q2ys" >>
markerLib.UNABBREV_TAC "q3ys" >>
Q.PAT_ABBREV_TAC `q3ys = (mw_mul_by_single q3 (REVERSE ys))` >>
Q.PAT_ABBREV_TAC `w = FST (mw_sub (REVERSE us) q3ys T)` >>
Q.PAT_ABBREV_TAC `zs2 = (REVERSE (FRONT w) ++ DROP (SUC (LENGTH ys)) zs)` >>
`LENGTH q3ys = LENGTH us` by METIS_TAC[Abbr`us`,Abbr`q3ys`,mw_mul_by_single_lemma,ADD1,LENGTH_TAKE,LESS_EQ,LENGTH_REVERSE] >>
`0 < LENGTH us /\ (LENGTH us = SUC(LENGTH ys))` by METIS_TAC[LENGTH_TAKE,LESS_EQ,DECIDE ``0 < SUC x``] >>
`0 < mw2n (REVERSE ys)` by
        (`ys <> []` by METIS_TAC[NOT_NIL_EQ_LENGTH_NOT_0,DECIDE ``0<1``,LESS_TRANS] >>
         `?h t. ys = h::t` by METIS_TAC[list_CASES] >>
         FULL_SIMP_TAC std_ss[HD] >>
         POP_ASSUM (fn x => lrw[x,mw2n_msf,dimwords_dimword]) >>
         `0 < dimword(:'a) DIV 2` by METIS_TAC[TWO,DIV_GT0,DECIDE``0<2``,TWO,LESS_EQ,ONE_LT_dimword] >>
         METIS_TAC[LESS_LESS_EQ_TRANS,ZERO_LT_EXP,ZERO_LT_dimword,LESS_EQ_ADD,ZERO_LESS_MULT,ADD_COMM]) >>
`w2n q3 = mw2n (REVERSE us) DIV mw2n (REVERSE ys)` by ALL_TAC
THENL[`(w2n q2 = mw2n (REVERSE us) DIV mw2n (REVERSE ys)) \/(w2n q2 = SUC (mw2n (REVERSE us) DIV mw2n (REVERSE ys)))` by tac_div_loop_test
       THEN1(`mw2n (REVERSE us) < mw2n (mw_mul_by_single q2 (REVERSE ys))` by FULL_SIMP_TAC std_ss[ADD1,LENGTH,LENGTH_REVERSE,mw_mul_by_single_lemma,mw_cmp_thm] >>
            POP_ASSUM (fn x => ASSUME_TAC (RW[mw_mul_by_single_lemma] x)) >>
            qpat_x_assum `w2n q2 = xxx` (fn x => FULL_SIMP_TAC std_ss [x]) >>
            METIS_TAC[NOT_LESS,DIV_thm3]) >>
       METIS_TAC[SUC_SUB1,w2n_n2w,w2n_lt,LESS_MOD,DECIDE ``x < SUC x``,LESS_TRANS,Abbr`q3`],
      ALL_TAC,
      `(w2n q3 = mw2n (REVERSE us) DIV mw2n (REVERSE ys)) \/(w2n q3 = SUC (mw2n (REVERSE us) DIV mw2n (REVERSE ys)))` by tac_div_loop_test >>
      `LENGTH q3ys = LENGTH (REVERSE us)` by METIS_TAC[ADD1,LENGTH,LENGTH_REVERSE,mw_mul_by_single_lemma,Abbr`q3ys`] >>
      `mw2n q3ys <= mw2n (REVERSE us)` by FULL_SIMP_TAC std_ss[mw_cmp_thm,NOT_LESS] >>
      markerLib.UNABBREV_TAC "q3ys" >>
      POP_ASSUM (fn x => ASSUME_TAC (RW[mw_mul_by_single_lemma] x)) >>
      qpat_x_assum `w2n q3 = xxx` (fn x => FULL_SIMP_TAC std_ss [x]) >>
      METIS_TAC[X_LE_DIV,NOT_LESS,DECIDE ``z < SUC z``],
      ALL_TAC] >>
`w <> [] /\ (LENGTH w = SUC(LENGTH ys))` by METIS_TAC[mw_sub_lemma,PAIR,LENGTH_REVERSE,NOT_NIL_EQ_LENGTH_NOT_0] >>
`LENGTH zs = SUC (LENGTH zs2)` by (
      markerLib.UNABBREV_TAC "zs2" >>
      REWRITE_TAC[LENGTH_APPEND,LENGTH_REVERSE,LENGTH_DROP] >>
      srw_tac[][rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
      RW_TAC arith_ss[]) >>
`mw2n q3ys <= mw2n (REVERSE us)` by METIS_TAC[Abbr`q3ys`,mw_mul_by_single_lemma,DIV_thm3] >>
`mw2n w = mw2n (REVERSE us) - mw2n q3ys` by METIS_TAC[LENGTH_REVERSE,mw_sub_thm] >>
`mw2n (FRONT w) = mw2n w` by(
       `mw2n w < dimword(:'a) ** LENGTH (FRONT w)` by (
                qpat_x_assum `mw2n xx = mw2n yy - mw2n zz` (K ALL_TAC) >>
                srw_tac[][rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
                `mw2n w = mw2n (REVERSE us) - mw2n q3ys` by METIS_TAC[LENGTH_REVERSE,mw_sub_thm] >>
                POP_ASSUM (fn x => REWRITE_TAC[x]) >>
                markerLib.UNABBREV_TAC "q3ys" >>
                ASM_REWRITE_TAC[mw_mul_by_single_lemma] >>
                METIS_TAC[DIV_thm4,LESS_TRANS,mw2n_lt,dimwords_dimword,LENGTH_REVERSE]) >>
       METIS_TAC[mw2n_msf_NIL,dimwords_dimword]) >>
Cases_on `LENGTH ys < LENGTH zs2`
THENL[tac_div_loop_1,tac_div_loop_2,tac_div_loop_1,tac_div_loop_2]);

val tac_div_loop_bis_1 =
    `0 < LENGTH zs2` by DECIDE_TAC >>
    `LENGTH ys <= LENGTH (mw_div_loop zs2 ys)` by METIS_TAC[NOT_NIL_EQ_LENGTH_NOT_0,mw_div_loop_LENGTH,LESS_IMP_LESS_OR_EQ] >>
    srw_tac[][LASTN_CONS] >>
    `mw2n (REVERSE (TAKE (SUC (LENGTH ys)) zs2)) DIV mw2n (REVERSE ys) < dimword (:'a)` by ALL_TAC
    THEN1(    `SUC (LENGTH ys) < LENGTH zs` by DECIDE_TAC >>
              markerLib.UNABBREV_TAC "zs2" >>
              `LENGTH (FRONT w) = LENGTH ys` by METIS_TAC[prim_recTheory.PRE,LENGTH_BUTLAST] >>
              `LENGTH (REVERSE (FRONT w)) < SUC (LENGTH ys)` by METIS_TAC[LENGTH_REVERSE,DECIDE ``x < SUC x``] >>
              srw_tac[][TAKE_APPEND2,REVERSE_APPEND,SUC_SUB] >>
              `LENGTH (TAKE 1 (DROP (SUC (LENGTH ys)) zs)) = 1` by METIS_TAC[LENGTH_TAKE,LENGTH_DROP,LESS_EQ,SUB_LESS_0,ONE] >>
              srw_tac[][mw2n_APPEND,dimwords_dimword] >>
              `!a b. (a < b * mw2n (REVERSE ys) ==> a DIV mw2n (REVERSE ys) < b)` by METIS_TAC[DIV_LT_X] >>
              POP_ASSUM (fn x => MATCH_MP_TAC x) >>
              MATCH_MP_TAC LESS_LESS_EQ_TRANS >> EXISTS_TAC ``dimword(:'a) * SUC (mw2n (REVERSE (us:'a word list)) - mw2n (q3ys:'a word list))`` >>
              strip_tac
              THEN1( REWRITE_TAC[METIS_PROVE [MULT,MULT_COMM,ADD_COMM] ``a * SUC b = a + a * b``] >>
                      `!(x:num). x ** 1 = x` by
                     (GEN_TAC >> REWRITE_TAC[ONE,Q.SPECL [`x`,`0`] (CONJUNCT2 EXP)] >>
                     RW_TAC arith_ss[]) >>
                     MATCH_MP_TAC LESS_MONO_ADD >>
                     METIS_TAC[LESS_MONO_ADD,mw2n_lt,dimwords_dimword,LENGTH_REVERSE]) >>
              markerLib.UNABBREV_TAC "q3ys" >>
              ASM_REWRITE_TAC[mw_mul_by_single_lemma] >>
              METIS_TAC[LESS_MONO_MULT,MULT_COMM,DIV_thm4,LESS_EQ]) >>
     METIS_TAC[];

val tac_div_loop_bis_2 =
srw_tac[][Once mw_div_loop_def] >>
lrw[rich_listTheory.LASTN_CONS,rich_listTheory.LASTN_LENGTH_ID] >>
markerLib.UNABBREV_TAC "zs2" >>
`SUC (LENGTH ys) = LENGTH zs` by DECIDE_TAC >>
POP_ASSUM (fn x => REWRITE_TAC[x]) >>
REWRITE_TAC[REVERSE_APPEND,REVERSE_REVERSE,rich_listTheory.BUTFIRSTN_LENGTH_NIL,REVERSE,APPEND_NIL] >>
`LENGTH (REVERSE (FRONT w)) = LENGTH ys` by METIS_TAC[rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE,LENGTH_REVERSE] >>
POP_ASSUM (fn x => ASM_REWRITE_TAC[GSYM x,LASTN_LENGTH_ID,REVERSE_REVERSE]) >>
markerLib.UNABBREV_TAC "q3ys" >>
ASM_REWRITE_TAC[mw_mul_by_single_lemma] >>
METIS_TAC[DIV_thm4];

val mw_div_loop_thm_bis = store_thm ("mw_div_loop_thm_bis",
``!(zs:'a word list) (ys:'a word list).
  dimword(:'a) DIV 2 <= w2n (HD ys) /\
  LENGTH ys < LENGTH zs /\ 1 < LENGTH ys /\
  ((mw2n (REVERSE (TAKE (SUC (LENGTH ys)) zs)) DIV mw2n (REVERSE ys)) < dimword(:'a) ) ==>
  (let rslt = mw_div_loop zs ys in
   (mw2n (REVERSE( BUTLASTN (LENGTH ys) rslt)) = mw2n (REVERSE zs) DIV mw2n (REVERSE ys)) /\
   (mw2n (REVERSE (LASTN (LENGTH ys) rslt)) = mw2n (REVERSE zs) MOD mw2n (REVERSE ys)))``,

qsuff_tac `!(zs:'a word list) (ys:'a word list).
           dimword(:'a) DIV 2 <= w2n (HD ys) /\
           LENGTH ys < LENGTH zs /\ 1 < LENGTH ys /\
           ((mw2n (REVERSE (TAKE (SUC (LENGTH ys)) zs)) DIV mw2n (REVERSE ys)) < dimword(:'a) ) ==>
           (mw2n (REVERSE (LASTN (LENGTH ys) (mw_div_loop zs ys))) < mw2n (REVERSE ys))`
THEN1(REPEAT strip_tac >>
      srw_tac[][] >>
      IMP_RES_TAC mw_div_loop_thm >>
      `mw2n (REVERSE zs) = mw2n (REVERSE (BUTLASTN (LENGTH ys) rslt)) * mw2n (REVERSE ys) +
       mw2n (REVERSE (LASTN (LENGTH ys) rslt))` by METIS_TAC[] >>
      POP_ASSUM (fn x => REWRITE_TAC[x]) >>
      `0 < mw2n (REVERSE ys)` by
        (`ys <> []` by METIS_TAC[NOT_NIL_EQ_LENGTH_NOT_0,DECIDE ``0<1``,LESS_TRANS] >>
         `?h t. ys = h::t` by METIS_TAC[list_CASES] >>
         FULL_SIMP_TAC std_ss[HD] >>
         POP_ASSUM (fn x => lrw[x,mw2n_msf,dimwords_dimword]) >>
         `0 < dimword(:'a) DIV 2` by METIS_TAC[TWO,DIV_GT0,DECIDE``0<2``,TWO,LESS_EQ,ONE_LT_dimword] >>
         METIS_TAC[LESS_LESS_EQ_TRANS,ZERO_LT_EXP,ZERO_LT_dimword,LESS_EQ_ADD,ZERO_LESS_MULT,ADD_COMM]) >>
      srw_tac[][MOD_TIMES,ADD_DIV_ADD_DIV,Abbr`rslt`] >>
      MATCH_MP_TAC ((fn (x,y) => y) (EQ_IMP_RULE (SPEC_ALL EQ_ADDL))) >>
      MATCH_MP_TAC LESS_DIV_EQ_ZERO >> METIS_TAC[]) >>

HO_MATCH_MP_TAC mw_div_loop_ind >>
REPEAT strip_tac >>
srw_tac[][Once mw_div_loop_def] >>
Cases_on `mw_cmp (REVERSE us) q2ys = SOME T` >>
markerLib.UNABBREV_TAC "q3"
THENL[Q.PAT_ABBREV_TAC`(q3:'a word) = n2w (w2n q2 - 1)`,markerLib.UNABBREV_TAC "q2" >>
      Q.PAT_ABBREV_TAC `q3 = mw_div_test q (HD us) (HD (TL us)) (HD (TL (TL us))) (HD ys) (HD (TL ys))`] >>
markerLib.UNABBREV_TAC "zs2" >>
markerLib.UNABBREV_TAC "zs2'" >>
markerLib.UNABBREV_TAC "q2ys" >>
markerLib.UNABBREV_TAC "q3ys" >>
Q.PAT_ABBREV_TAC `q3ys = (mw_mul_by_single q3 (REVERSE ys))` >>
Q.PAT_ABBREV_TAC `w = FST (mw_sub (REVERSE us) q3ys T)` >>
Q.PAT_ABBREV_TAC `zs2 = (REVERSE (FRONT w) ++ DROP (SUC (LENGTH ys)) zs)` >>
srw_tac[][] >>
`0 < LENGTH us /\ (LENGTH us = SUC(LENGTH ys))` by METIS_TAC[LENGTH_TAKE,LESS_EQ,DECIDE ``0 < SUC x``] >>
`LENGTH q3ys = LENGTH us` by METIS_TAC[Abbr`us`,Abbr`q3ys`,mw_mul_by_single_lemma,ADD1,LENGTH_TAKE,LESS_EQ,LENGTH_REVERSE] >>
`0 < mw2n (REVERSE ys)` by
        (`ys <> []` by METIS_TAC[NOT_NIL_EQ_LENGTH_NOT_0,DECIDE ``0<1``,LESS_TRANS] >>
         `?h t. ys = h::t` by METIS_TAC[list_CASES] >>
         FULL_SIMP_TAC std_ss[HD] >>
         POP_ASSUM (fn x => lrw[x,mw2n_msf,dimwords_dimword]) >>
         `0 < dimword(:'a) DIV 2` by METIS_TAC[TWO,DIV_GT0,DECIDE``0<2``,TWO,LESS_EQ,ONE_LT_dimword] >>
         METIS_TAC[LESS_LESS_EQ_TRANS,ZERO_LT_EXP,ZERO_LT_dimword,LESS_EQ_ADD,ZERO_LESS_MULT,ADD_COMM]) >>
`w2n q3 = mw2n (REVERSE us) DIV mw2n (REVERSE ys)` by ALL_TAC
THENL[`(w2n q2 = mw2n (REVERSE us) DIV mw2n (REVERSE ys)) \/(w2n q2 = SUC (mw2n (REVERSE us) DIV mw2n (REVERSE ys)))` by tac_div_loop_test
       THEN1(`mw2n (REVERSE us) < mw2n (mw_mul_by_single q2 (REVERSE ys))` by FULL_SIMP_TAC std_ss[ADD1,LENGTH,LENGTH_REVERSE,mw_mul_by_single_lemma,mw_cmp_thm] >>
            POP_ASSUM (fn x => ASSUME_TAC (RW[mw_mul_by_single_lemma] x)) >>
            qpat_x_assum `w2n q2 = xxx` (fn x => FULL_SIMP_TAC std_ss [x]) >>
            METIS_TAC[NOT_LESS,DIV_thm3]) >>
       METIS_TAC[SUC_SUB1,w2n_n2w,w2n_lt,LESS_MOD,DECIDE ``x < SUC x``,LESS_TRANS,Abbr`q3`],
      ALL_TAC,
      `(w2n q3 = mw2n (REVERSE us) DIV mw2n (REVERSE ys)) \/(w2n q3 = SUC (mw2n (REVERSE us) DIV mw2n (REVERSE ys)))` by tac_div_loop_test >>
      `LENGTH q3ys = LENGTH (REVERSE us)` by METIS_TAC[ADD1,LENGTH,LENGTH_REVERSE,mw_mul_by_single_lemma,Abbr`q3ys`] >>
      `mw2n q3ys <= mw2n (REVERSE us)` by FULL_SIMP_TAC std_ss[mw_cmp_thm,NOT_LESS] >>
      markerLib.UNABBREV_TAC "q3ys" >>
      POP_ASSUM (fn x => ASSUME_TAC (RW[mw_mul_by_single_lemma] x)) >>
      qpat_x_assum `w2n q3 = xxx` (fn x => FULL_SIMP_TAC std_ss [x]) >>
      METIS_TAC[X_LE_DIV,NOT_LESS,DECIDE ``z < SUC z``],
      ALL_TAC] >>
`mw2n q3ys <= mw2n (REVERSE us)` by METIS_TAC[Abbr`q3ys`,mw_mul_by_single_lemma,DIV_thm3] >>
`w <> [] /\ (LENGTH w = SUC(LENGTH ys))` by METIS_TAC[mw_sub_lemma,PAIR,LENGTH_REVERSE,NOT_NIL_EQ_LENGTH_NOT_0] >>
`mw2n w = mw2n (REVERSE us) - mw2n q3ys` by METIS_TAC[Abbr`w`,LENGTH_REVERSE,mw_sub_thm] >>
`mw2n (FRONT w) = mw2n w` by (
       `mw2n w < dimword(:'a) ** LENGTH (FRONT w)` by (
                qpat_x_assum `mw2n xx = mw2n yy - mw2n zz` (fn x => (
                    srw_tac[][rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
                    ASSUME_TAC x)) >>
                POP_ASSUM (fn x => REWRITE_TAC[x]) >>
                markerLib.UNABBREV_TAC "q3ys" >>
                ASM_REWRITE_TAC[mw_mul_by_single_lemma] >>
                METIS_TAC[DIV_thm4,LESS_TRANS,mw2n_lt,dimwords_dimword,LENGTH_REVERSE]) >>
       METIS_TAC[mw2n_msf_NIL,dimwords_dimword]) >>
`LENGTH zs = SUC (LENGTH zs2)` by (
      markerLib.UNABBREV_TAC "zs2" >>
      REWRITE_TAC[LENGTH_APPEND,LENGTH_REVERSE,LENGTH_DROP] >>
      srw_tac[][rich_listTheory.LENGTH_BUTLAST,prim_recTheory.PRE] >>
      RW_TAC arith_ss[]) >>
Cases_on `LENGTH ys < LENGTH zs2`
THENL[tac_div_loop_bis_1,tac_div_loop_bis_2,tac_div_loop_bis_1,tac_div_loop_bis_2]);

val mw_div_guess_def = Define `
  mw_div_guess us (ys:'a word list) =
    let q = if w2n (HD us) < w2n (HD ys) then
              FST (single_div (HD us) (HD (TL us)) (HD ys))
            else n2w (dimword (:'a) - 1) in
    let q2 = mw_div_test q (HD us) (HD (TL us)) (HD (TL (TL us)))
                         (HD ys) (HD (TL ys)) in
      q2`;

val mw_div_adjust_def = Define `
  mw_div_adjust q zs ys =
    if mw_cmp zs (mw_mul_by_single q ys) = SOME T then n2w (w2n q - 1) else q`;

val mw_div_aux_def = tDefine "mw_div_aux" `
  mw_div_aux zs1 zs2 ys =
    if zs1 = [] then ([],zs2) else
      let zs2 = (LAST zs1) :: zs2 in
      let zs1 = BUTLAST zs1 in
      let q = mw_div_guess (REVERSE zs2) (REVERSE ys) in
      let q = mw_div_adjust q zs2 ys in
      let zs2 = FST (mw_sub zs2 (mw_mul_by_single q ys) T) in
      let (qs,rs) = mw_div_aux zs1 (FRONT zs2) ys in
        (q::qs,rs)`
  (WF_REL_TAC `measure (\(zs1,zs2,ys). LENGTH zs1)`
   \\ SIMP_TAC std_ss [LENGTH_FRONT,DECIDE ``PRE n = n - 1``]
   \\ SIMP_TAC std_ss [GSYM LENGTH_NIL] \\ DECIDE_TAC);

val mw_div_aux_ind = fetch "-" "mw_div_aux_ind"

val mw_div_loop_alt_lemma = Q.prove(
  `mw_div_loop zs ys =
     if LENGTH ys < LENGTH zs then
       (let us = TAKE (SUC (LENGTH ys)) zs in
        let q2 = mw_div_guess us ys in
        let q2ys = mw_mul_by_single q2 (REVERSE ys)
        in
          if mw_cmp (REVERSE us) q2ys = SOME T then
            (let q3 = n2w (w2n q2 - 1) in
             let q3ys = mw_mul_by_single q3 (REVERSE ys) in
             let zs2 =
                   REVERSE (FRONT (FST (mw_sub (REVERSE us) q3ys T))) ++
                   DROP (SUC (LENGTH ys)) zs
             in
               q3::mw_div_loop zs2 ys)
          else
            (let zs2 =
                   REVERSE (FRONT (FST (mw_sub (REVERSE us) q2ys T))) ++
                   DROP (SUC (LENGTH ys)) zs
             in
               q2::mw_div_loop zs2 ys))
     else zs`,
  SIMP_TAC std_ss [Once mw_div_loop_def]
  \\ SIMP_TAC std_ss [mw_div_guess_def,LET_DEF]);

val mw_div_loop_alt = Q.prove(
  `mw_div_loop zs ys =
     if LENGTH ys < LENGTH zs then
       (let us = TAKE (SUC (LENGTH ys)) zs in
        let q2 = mw_div_guess us ys in
        let q3 = mw_div_adjust q2 (REVERSE us) (REVERSE ys) in
        let q3ys = mw_mul_by_single q3 (REVERSE ys) in
        let zs2 = REVERSE (FRONT (FST (mw_sub (REVERSE us) q3ys T))) ++
                  DROP (SUC (LENGTH ys)) zs in
          q3::mw_div_loop zs2 ys)
     else zs`,
  SIMP_TAC std_ss [Once mw_div_loop_alt_lemma,mw_div_adjust_def]
  \\ Cases_on `LENGTH ys < LENGTH zs` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `mw_cmp (REVERSE (TAKE (SUC (LENGTH ys)) zs))
       (mw_mul_by_single (mw_div_guess (TAKE (SUC (LENGTH ys)) zs) ys)
          (REVERSE ys)) = SOME T` \\ FULL_SIMP_TAC std_ss []);

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> (b1 ==> b2) ==> b3``

val LENGTH_mw_sub = store_thm("LENGTH_mw_sub",
  ``!xs1 ys c qs1 c1. (mw_sub xs1 ys c = (qs1,c1)) ==> (LENGTH xs1 = LENGTH qs1)``,
  Induct \\ Cases_on `ys`
  \\ FULL_SIMP_TAC std_ss [mw_sub_def,LET_DEF,single_add_def,single_sub_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ REPEAT STRIP_TAC THEN1
   (Q.ABBREV_TAC `t = (dimword (:'a) <= w2n h + w2n (~0w:'a word) + b2n c)`
    \\ `?x1 x2. mw_sub xs1 [] t = (x1,x2)` by METIS_TAC [PAIR]
    \\ RES_TAC \\ Cases_on `qs1` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.ABBREV_TAC `tt = (dimword (:'a) <= w2n h' + w2n (~h) + b2n c)`
  \\ `?x1 x2. mw_sub xs1 t tt = (x1,x2)` by METIS_TAC [PAIR]
  \\ RES_TAC \\ Cases_on `qs1` \\ FULL_SIMP_TAC (srw_ss()) []);

val mw_div_aux_lemma = prove(
  ``!zs1 zs2 ys qs rs.
      (LENGTH zs2 = LENGTH ys) /\ 1 < LENGTH ys /\
      (mw_div_aux zs1 zs2 ys = (qs,rs)) ==>
      (mw_div_loop (REVERSE (zs1 ++ zs2)) (REVERSE ys) =
         qs ++ REVERSE rs) /\ (LENGTH rs = LENGTH ys)``,
  STRIP_TAC \\ completeInduct_on `LENGTH zs1` \\ NTAC 2 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ NTAC 5 STRIP_TAC
  \\ `(zs1 = []) \/ ?x l. zs1 = SNOC x l` by METIS_TAC [SNOC_CASES] THEN1
   (FULL_SIMP_TAC std_ss [APPEND,EVAL ``mw_div_aux [] zs2 ys``]
    \\ ONCE_REWRITE_TAC [mw_div_loop_def]
    \\ Q.PAT_X_ASSUM `[] = qs` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [APPEND])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `mw_div_aux (SNOC x l) zs2 ys = (qs,rs)` MP_TAC
  \\ SIMP_TAC std_ss [Once mw_div_aux_def,LAST_SNOC,FRONT_SNOC]
  \\ FULL_SIMP_TAC std_ss [REVERSE_APPEND,SNOC_APPEND,APPEND_ASSOC]
  \\ ONCE_REWRITE_TAC [mw_div_loop_alt]
  \\ FULL_SIMP_TAC (srw_ss()) [DECIDE ``n < n + 1 + m:num``]
  \\ SIMP_TAC std_ss [Once LET_DEF]
  \\ SIMP_TAC std_ss [Once LET_DEF] \\ STRIP_TAC
  \\ `TAKE (SUC (LENGTH ys)) (REVERSE zs2 ++ [x] ++ REVERSE l) =
      REVERSE zs2 ++ [x]` by ALL_TAC THEN1
   (`SUC (LENGTH ys) = LENGTH (REVERSE zs2 ++ [x])` by ALL_TAC
    THEN1 FULL_SIMP_TAC (srw_ss()) [ADD1]
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.TAKE_LENGTH_APPEND,APPEND_ASSOC])
  \\ ASM_SIMP_TAC std_ss [Once LET_DEF]
  \\ FULL_SIMP_TAC std_ss [REVERSE_DEF]
  \\ Q.ABBREV_TAC `q2 = mw_div_guess (REVERSE zs2 ++ [x]) (REVERSE ys)`
  \\ FULL_SIMP_TAC std_ss [REVERSE_APPEND,REVERSE_REVERSE,REVERSE_DEF,APPEND]
  \\ SIMP_TAC (srw_ss()) [Once LET_DEF]
  \\ Q.PAT_X_ASSUM `exp = (xx,yy)` MP_TAC
  \\ SIMP_TAC (srw_ss()) [Once LET_DEF]
  \\ Q.ABBREV_TAC `qq = mw_div_adjust q2 (x::zs2) ys`
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `ts = (FRONT (FST (mw_sub (x::zs2) (mw_mul_by_single qq ys) T)))`
  \\ `DROP (SUC (LENGTH ys)) (REVERSE zs2 ++ [x] ++ REVERSE l) =
      REVERSE l` by ALL_TAC THEN1
   (`SUC (LENGTH ys) = LENGTH (REVERSE zs2 ++ [x])` by ALL_TAC
    THEN1 FULL_SIMP_TAC (srw_ss()) [ADD1]
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.DROP_LENGTH_APPEND,APPEND_ASSOC])
  \\ FULL_SIMP_TAC std_ss []
  \\ `?qs1 rs1. mw_div_aux l ts ys = (qs1,rs1)` by METIS_TAC [PAIR]
  \\ Q.PAT_X_ASSUM `!xxx. bbb` (MP_TAC o Q.SPECL [`l`,`ts`,`ys`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (Q.UNABBREV_TAC `ts`
    \\ `?w1 w2. mw_sub (x::zs2) (mw_mul_by_single qq ys) T = (w1,w2)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC LENGTH_mw_sub
    \\ Cases_on `w1` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC (srw_ss()) []);

val mw_div_def = Define `
  mw_div xs ys =
    let xs = mw_fix xs in
    let ys = mw_fix ys in
      if LENGTH xs < LENGTH ys then
        ([],xs ++ REPLICATE (LENGTH ys - LENGTH xs) 0w,T)
      else if LENGTH ys = 1 then
        let (qs,r,c) = mw_simple_div 0w (REVERSE xs) (HD ys) in
          (REVERSE qs,[r],c)
      else
        let d = calc_d (LAST ys,0x1w) in
        let xs = mw_mul_by_single d xs ++ [0w] in
        let xs1 = BUTLASTN (LENGTH ys) xs in
        let xs2 = LASTN (LENGTH ys) xs in
        let ys = FRONT (mw_mul_by_single d ys) in
        let (qs,rs) = mw_div_aux xs1 xs2 ys in
        let (rs,r,c) = mw_simple_div 0w (REVERSE rs) d in
          (REVERSE qs,REVERSE rs,c)`

val mwi_divmod_def = Define `
  mwi_divmod (s,xs) (t,ys) =
    let (res,mod,c) = mw_div xs ys in
    let res = mw_fix res in
    let mod = mw_fix mod in
    let res = if s = t then res else
              if mod = [] then res else mw_addv res [] T in
    let res_sign = (if res = [] then F else ~(s = t)) in
    let mod = if s = t then mod else
              if mod = [] then mod else mw_subv ys mod in
    let mod_sign = (if mod = [] then F else t) in
      (c,(res_sign,res),(mod_sign,mod))`;

val mwi_div_def = Define `
  mwi_div s_xs t_ys = FST (SND (mwi_divmod s_xs t_ys))`;

val mwi_mod_def = Define `
  mwi_mod s_xs t_ys = SND (SND (mwi_divmod s_xs t_ys))`;

val MULT_DIV_MULT_EQ_MULT = Q.prove(
  `!n k m. 0 < n /\ 0 < k ==> ((m * n) DIV (k * n) = m DIV k)`,
  ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [GSYM DIV_DIV_DIV_MULT,RW1 [MULT_COMM] MULT_DIV]);

val LENGTH_mw_simple_div = store_thm("LENGTH_mw_simple_div",
  ``!xs x ys qs r c.
      (mw_simple_div x xs ys = (qs,r,c)) ==> (LENGTH xs = LENGTH qs)``,
  Induct \\ SIMP_TAC std_ss [mw_simple_div_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `single_div x h ys`
  \\ FULL_SIMP_TAC std_ss []
  \\ `?qs1 r1 c1. mw_simple_div r' xs ys = (qs1,r1,c1)` by METIS_TAC [PAIR]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `q::qs1 = qs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH]);

val mw_div_thm = store_thm("mw_div_thm",
  ``!xs ys mod res c.
      (mw_div xs ys = (res,mod,c)) /\ mw2n ys <> 0 ==>
      (mw2n res = mw2n xs DIV mw2n ys) /\
      (mw2n mod = mw2n xs MOD mw2n ys) /\ c /\ (LENGTH mod = LENGTH (mw_fix ys))``,
  NTAC 5 STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [LET_DEF,mw_div_def]
  \\ Cases_on `LENGTH (mw_fix xs) < LENGTH (mw_fix ys)`
  \\ FULL_SIMP_TAC std_ss [mw2n_mw_fix] THEN1
   (IMP_RES_TAC LENGTH_LESS_IMP_mw2n_LESS \\ FULL_SIMP_TAC std_ss
      [mw_ok_mw_fix,mw2n_mw_fix,mw2n_def,GSYM mw2n_APPEND_REPLICATE]
    \\ `0 < mw2n ys` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [DIV_EQ_X]
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REPLICATE]
    \\ REPEAT STRIP_TAC \\ DECIDE_TAC)
  \\ Cases_on `LENGTH (mw_fix ys) = 1` \\ ASM_SIMP_TAC std_ss [] THEN1
   (Cases_on `mw_fix ys` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [HD] \\ STRIP_TAC
    \\ `?qs r b. mw_simple_div 0w (REVERSE (mw_fix xs)) h = (qs,r,b)` by
         METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [mw2n_def]
    \\ `mw2n ys = mw2n (mw_fix ys)` by FULL_SIMP_TAC std_ss [mw2n_mw_fix]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [mw2n_def] \\ NTAC 2 STRIP_TAC
    \\ `0w <+ h` by ALL_TAC THEN1
      (Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [word_lo_n2w] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC mw_simple_div_thm \\ FULL_SIMP_TAC (srw_ss()) [mw2n_mw_fix]
    \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [w2n_n2w,mw2n_def])
  \\ Q.ABBREV_TAC `d = (calc_d (LAST (mw_fix ys),0x1w))`
  \\ Q.ABBREV_TAC `xs1 = (mw_mul_by_single d (mw_fix xs) ++ [0x0w])`
  \\ Q.ABBREV_TAC `ys1 = (FRONT (mw_mul_by_single d (mw_fix ys)))`
  \\ `?qs1 rs1. mw_div_aux (BUTLASTN (LENGTH (mw_fix ys)) xs1)
       (LASTN (LENGTH (mw_fix ys)) xs1) ys1 = (qs1,rs1)` by METIS_TAC [PAIR]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ MP_TAC (mw_div_aux_lemma |> Q.SPECL [
      `(BUTLASTN (LENGTH (mw_fix (ys:'a word list))) xs1:'a word list)`,
      `(LASTN (LENGTH (mw_fix (ys:'a word list))) xs1:'a word list)`,`ys1`])
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ FULL_SIMP_TAC std_ss [LENGTH_DROP]
  \\ `LENGTH xs1 = LENGTH (mw_fix xs) + 2` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `xs1`
    \\ SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,mw_mul_by_single_def,
         LENGTH_mw_mul_pass] \\ DECIDE_TAC)
  \\ `LENGTH ys1 = LENGTH (mw_fix ys)` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `ys1`
    \\ `mw_mul_by_single d (mw_fix ys) <> []` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL]
      \\ SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,mw_mul_by_single_def,
           LENGTH_mw_mul_pass])
    \\ FULL_SIMP_TAC std_ss [LENGTH_FRONT]
    \\ SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,mw_mul_by_single_def,
         LENGTH_mw_mul_pass] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH (mw_fix ys) <> 0` by ALL_TAC THEN1
        (FULL_SIMP_TAC std_ss [LENGTH_NIL,mw_fix_NIL])
  \\ `LENGTH (mw_fix ys) <= LENGTH xs1` by
        (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC APPEND_BUTLASTN_LASTN \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ REPEAT (MATCH_MP_TAC LENGTH_LASTN) \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ `mw2n xs1 = mw2n xs * w2n d` by ALL_TAC THEN1
    (Q.UNABBREV_TAC `xs1` \\ FULL_SIMP_TAC (srw_ss()) [AC MULT_COMM MULT_ASSOC,
      mw2n_APPEND,mw2n_def,mw_mul_by_single_lemma,mw2n_mw_fix])
  \\ `0 < w2n (LAST (mw_fix ys))` by ALL_TAC THEN1
   (`mw_ok (mw_fix ys)` by FULL_SIMP_TAC std_ss [mw_ok_mw_fix]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [mw_ok_def,LENGTH_NIL]
    \\ Cases_on `LAST (mw_fix ys)` \\ SRW_TAC [] [] \\ DECIDE_TAC)
  \\ `FRONT (mw_mul_by_single d (mw_fix ys)) <> []` by ALL_TAC THEN1
   (`mw_mul_by_single d (mw_fix ys) <> []` by ALL_TAC
    \\ SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_FRONT,mw_mul_by_single_def,
         LENGTH_mw_mul_pass] \\ DECIDE_TAC)
  \\ `(mw2n ys1 = mw2n ys * w2n d) /\
      dimword (:'a) DIV 2 <= w2n (HD (REVERSE ys1))` by ALL_TAC THEN1
    (Q.UNABBREV_TAC `ys1` \\ FULL_SIMP_TAC (srw_ss()) [AC MULT_COMM MULT_ASSOC,
      mw2n_APPEND,mw2n_def,mw_mul_by_single_lemma,mw2n_mw_fix]
     \\ IMP_RES_TAC (GSYM d_clauses)
     \\ POP_ASSUM (MP_TAC o Q.SPEC `REVERSE (BUTLAST (mw_fix ys))`)
     \\ POP_ASSUM (MP_TAC o Q.SPEC `REVERSE (BUTLAST (mw_fix ys))`)
     \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,REVERSE_DEF,APPEND_FRONT_LAST]
     \\ FULL_SIMP_TAC std_ss [mw_mul_by_single_lemma,mw2n_mw_fix,
         AC MULT_COMM MULT_ASSOC,HD_REVERSE])
  \\ MP_TAC (mw_div_loop_thm_bis |> Q.SPECL [`REVERSE xs1`,`REVERSE ys1`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [REVERSE_REVERSE,LENGTH_REVERSE]
    \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ IMP_RES_TAC (GSYM d_clauses) \\ POP_ASSUM (K ALL_TAC)
    \\ `0 < (mw2n ys * w2n d)` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `d`
      \\ FULL_SIMP_TAC (srw_ss()) [DECIDE ``0 < n <=> n <> 0:num``])
    \\ ASM_SIMP_TAC std_ss [DIV_LT_X]
    \\ Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND,APPEND,
         REVERSE_DEF,TAKE,mw2n_APPEND,mw2n_def]
    \\ MATCH_MP_TAC LESS_LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `dimwords (LENGTH (mw_fix ys)) (:'a)`
    \\ STRIP_TAC THEN1
     (`LENGTH (REVERSE
        (TAKE (LENGTH (mw_fix ys))
          (REVERSE (mw_mul_by_single d (mw_fix xs))))) =
       LENGTH (mw_fix ys)` by ALL_TAC THEN1
        (FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ MATCH_MP_TAC LENGTH_TAKE
         \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE,LENGTH_mw_mul_by_single]
         \\ DECIDE_TAC)
      \\ METIS_TAC [mw2n_lt])
    \\ ONCE_REWRITE_TAC [GSYM mw2n_mw_fix]
    \\ `mw_ok (mw_fix ys)` by FULL_SIMP_TAC std_ss [mw_ok_mw_fix]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [mw_ok_def,LENGTH_NIL]
    \\ STRIP_TAC
    \\ `?x l. mw_fix ys = SNOC x l` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [LAST_SNOC,LENGTH_SNOC]
    \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,mw2n_APPEND,mw2n_def,dimwords_SUC]
    \\ SIMP_TAC std_ss [Once MULT_COMM] \\ DISJ2_TAC
    \\ Cases_on `x` \\ Cases_on `d` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LET_DEF,REVERSE_REVERSE,LENGTH_REVERSE]
  \\ `(LENGTH (mw_fix ys)) = LENGTH (REVERSE rs1)` by ALL_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [LENGTH_REVERSE])
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [rich_listTheory.BUTLASTN_LENGTH_APPEND]
  \\ SIMP_TAC std_ss [rich_listTheory.LASTN_LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [REVERSE_REVERSE] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `xxx = (res,mod,c)` (ASSUME_TAC o GSYM)
  \\ `?n. w2n d = 2 ** n` by METIS_TAC [d_lemma4 |> SIMP_RULE std_ss []]
  \\ `?q2 r2 c2. mw_simple_div 0x0w (REVERSE rs1) d = (q2,r2,c2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ `0 < mw2n ys` by DECIDE_TAC
  \\ `0x0w <+ d` by ALL_TAC THEN1
   (Cases_on `d` \\ FULL_SIMP_TAC std_ss [w2n_n2w,WORD_LO,ZERO_LT_dimword])
  \\ MP_TAC (mw_simple_div_thm |> Q.SPECL [`REVERSE rs1`,`d`])
  \\ FULL_SIMP_TAC std_ss [REVERSE_REVERSE] \\ STRIP_TAC \\ STRIP_TAC
  THEN1 (MATCH_MP_TAC MULT_DIV_MULT_EQ_MULT \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,WORD_LO,
       GSYM (RW1 [MULT_COMM] DIV_MOD_MOD_DIV),MULT_DIV]
  \\ IMP_RES_TAC LENGTH_mw_simple_div
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE]);

val ABS_NEG = Q.prove(
  `ABS (-(& n)) = & n`,
  intLib.COOPER_TAC);

val NEG_DIV_LEMMA = Q.prove(
  `m <> 0 ==>
    ((- & n) / & m = - (& (n DIV m + if n MOD m = 0 then 0 else 1)):int)`,
  STRIP_TAC \\ `& m <> 0i` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC (srw_ss()) []
  \\ `0i < &m /\ (0 <= -&n = (n = 0))` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC std_ss [int_div,EVAL ``-0i``,NUM_OF_INT]
  \\ Cases_on `n = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`0 < m` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [ZERO_DIV] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [INT_MOD_CALCULATE,NUM_OF_INT]
  \\ Cases_on `n MOD m = 0` \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `k = n DIV m` \\ intLib.COOPER_TAC);

val NEG_DIV = Q.prove(
  `m <> 0 ==>
    (& n / & m         = (& (n DIV m)):int) /\
    ((- & n) / & m     = - (& (n DIV m + if n MOD m = 0 then 0 else 1)):int) /\
    (& n     / (- & m) = - (& (n DIV m + if n MOD m = 0 then 0 else 1)):int) /\
    ((- & n) / (- & m) = (& (n DIV m):int))`,
  STRIP_TAC \\ `& m <> 0i` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [NEG_DIV_LEMMA]);

val NEG_MOD_LEMMA = Q.prove(
  `m <> 0 ==>
    (-&n % &m = &(if n MOD m = 0 then 0 else m - n MOD m))`,
  STRIP_TAC \\ `& m <> 0i` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC std_ss [int_mod,NEG_DIV_LEMMA]
  \\ Cases_on `n MOD m = 0` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [integerTheory.INT_MUL_CALCULATE]
  \\ `0 < m` by DECIDE_TAC THEN1 (METIS_TAC [DIVISION,ADD_0])
  \\ IMP_RES_TAC DIVISION
  \\ REPEAT (Q.PAT_X_ASSUM `!k. bbb` (MP_TAC o GSYM o Q.SPEC `n`))
  \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [RIGHT_ADD_DISTRIB]
  \\ `n DIV m * m = n - n MOD m` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `&(n - n MOD m + m) = &(n - n MOD m) + & m` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [integerTheory.INT_ADD_CALCULATE]
  \\ FULL_SIMP_TAC std_ss []
  \\ `n MOD m <= n` by IMP_RES_TAC MOD_LESS_EQ
  \\ `n MOD m <= m` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM integerTheory.INT_SUB]
  \\ Q.ABBREV_TAC `k = n MOD m` \\ POP_ASSUM (K ALL_TAC)
  \\ intLib.COOPER_TAC);

val NEG_MOD = Q.prove(
  `m <> 0 ==>
    (& n % & m         = (& (n MOD m)):int) /\
    ((- & n) % & m     = &(if n MOD m = 0 then 0 else m - n MOD m)) /\
    (& n     % (- & m) = - &(if n MOD m = 0 then 0 else m - n MOD m)) /\
    ((- & n) % (- & m) = - (& (n MOD m):int))`,
  STRIP_TAC \\ `& m <> 0i` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [NEG_MOD_LEMMA]);

val mw_addv_lemma = Q.prove(
  `mw_addv (n2mw n) [] T = n2mw (n + 1)`,
  `mw_ok (mw_addv (n2mw n) [] T)` by ALL_TAC THEN1
    (MATCH_MP_TAC mw_ok_addv
     \\ FULL_SIMP_TAC std_ss [mw_ok_n2mw,EVAL ``mw_ok []``])
  \\ IMP_RES_TAC mw_ok_mw_mw2n
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ FULL_SIMP_TAC std_ss [mw2n_n2mw,mw_addv_thm,LENGTH]
  \\ AP_TERM_TAC \\ EVAL_TAC);

val Num_ABS_ID = Q.prove(
  `Num (ABS (& n)) = n`,
  intLib.COOPER_TAC);

val mw_subv_lemma = Q.prove(
  `j <> 0 ==>
    (mw_subv (n2mw (Num (ABS j))) (n2mw (Num (ABS i) MOD Num (ABS j))) =
     n2mw (Num (ABS j) - Num (ABS i) MOD Num (ABS j)))`,
  REPEAT STRIP_TAC \\ `0 < Num (ABS j)` by intLib.COOPER_TAC
  \\ Q.ABBREV_TAC `k = Num (ABS j)`
  \\ MATCH_MP_TAC IMP_EQ_n2mw_ALT
  \\ FULL_SIMP_TAC std_ss [mw_ok_n2mw,mw2n_n2mw]
  \\ STRIP_TAC THEN1 SIMP_TAC std_ss [mw_subv_def,mw_ok_mw_fix]
  \\ CONV_TAC (RAND_CONV (BINOP_CONV (ONCE_REWRITE_CONV [GSYM mw2n_n2mw])))
  \\ MATCH_MP_TAC mw_subv_thm
  \\ `Num (ABS i) MOD k < k` by FULL_SIMP_TAC std_ss [LESS_MOD]
  \\ FULL_SIMP_TAC std_ss [mw2n_n2mw] \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ MATCH_MP_TAC mw2n_LESS
  \\ FULL_SIMP_TAC std_ss [mw_ok_n2mw,mw2n_n2mw] \\ DECIDE_TAC);

val n2mw_EQ_NIL = Q.prove(
  `(n2mw n = []) <=> (n = 0)`,
  Cases_on `n` THEN1 EVAL_TAC \\ ONCE_REWRITE_TAC [n2mw_def]
  \\ SIMP_TAC std_ss [ADD1,NOT_CONS_NIL]);

val mwi_divmod_thm = store_thm("mwi_divmod_thm",
  ``!i j. j <> 0 ==>
      (mwi_divmod (i2mw i) ((i2mw j):bool # 'a word list) =
         (T,i2mw (i / j),i2mw (i % j)))``,
  NTAC 3 STRIP_TAC \\ SIMP_TAC std_ss [i2mw_def,mwi_divmod_def,n2mw_NIL,Num_ABS_EQ_0]
  \\ `(?r1 r2 r3. mw_div (n2mw (Num (ABS i))) (n2mw (Num (ABS j))) =
                 (r1:'a word list,r2,r3))`
         by METIS_TAC [PAIR] \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `mw2n (n2mw (Num (ABS j))) <> 0` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [mw2n_n2mw] \\ intLib.COOPER_TAC)
  \\ MP_TAC (mw_div_thm |> Q.SPECL [`n2mw (Num (ABS i))`,`n2mw (Num (ABS j))`])
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [mw2n_n2mw,n2mw_mw2n,mw_addv_lemma,
       n2mw_EQ_NIL,mw_subv_lemma]
  \\ STRIP_ASSUME_TAC (Q.SPEC `i` INT_NUM_CASES)
  \\ STRIP_ASSUME_TAC (Q.SPEC `j` INT_NUM_CASES)
  \\ FULL_SIMP_TAC (srw_ss()) [integerTheory.INT_ABS_NUM,ABS_NEG,NEG_DIV,NEG_MOD]
  \\ Cases_on `n MOD n' = 0` \\ FULL_SIMP_TAC std_ss [mw2n_n2mw]
  \\ `0 < n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [mw2n_n2mw,
        n2mw_EQ_NIL,EVAL ``n2mw 0``]);


(* converting into decimal form *)

val int_to_str_def = Define `
  int_to_str i =
    (if i < 0 then "~" else "") ++ num_to_dec_string (Num (ABS i))`;

val num_to_dec_string_unroll = Q.prove(
  `!n. num_to_dec_string n =
          SNOC (CHR (48 + n MOD 10))
               (if n < 10 then [] else num_to_dec_string (n DIV 10))`,
  SIMP_TAC std_ss [num_to_dec_string_def,n2s_def]
  \\ SIMP_TAC std_ss [Once numposrepTheory.n2l_def] \\ SRW_TAC [] []
  THEN1 (Cases_on `(n=0) \/ (n=1) \/ (n=2) \/ (n=3) \/ (n=4) \/
                   (n=5) \/ (n=6) \/ (n=7) \/ (n=8) \/ (n=9)`
         \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC \\ `F` by DECIDE_TAC)
  \\ `n MOD 10 < 10` by FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `k = n MOD 10`
  THEN1 (Cases_on `(k=0) \/ (k=1) \/ (k=2) \/ (k=3) \/ (k=4) \/
                   (k=5) \/ (k=6) \/ (k=7) \/ (k=8) \/ (k=9)`
         \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC \\ `F` by DECIDE_TAC));

val mw_to_dec_def = tDefine "mw_to_dec" `
  mw_to_dec (xs:'a word list) =
    if dimword (:'a) <= 10 then ([],F) else
      let (qs,r,c1) = mw_simple_div 0w (REVERSE xs) 10w in
      let qs = mw_fix (REVERSE qs) in
        if LENGTH qs = 0 then
          ([r + 48w],c1)
        else
          let (result,c2) = mw_to_dec qs in
            (result ++ [r + 48w],c1 /\ c2)`
 (WF_REL_TAC `measure (mw2n)` \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `(xx,yy) = zz` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ `0x0w <+ 10w` by FULL_SIMP_TAC (srw_ss()) [WORD_LO]
  \\ IMP_RES_TAC mw_simple_div_thm
  \\ FULL_SIMP_TAC (srw_ss()) [REVERSE_REVERSE,mw2n_mw_fix]
  \\ FULL_SIMP_TAC std_ss [DIV_LT_X,mw_fix_LENGTH_ZERO]
  \\ Q.PAT_X_ASSUM `10 < dimword (:'a)` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [DIV_EQ_X,NOT_LESS]
  \\ DECIDE_TAC);

val mwi_to_dec_def = Define `
  mwi_to_dec (s,xs) =
    let sign = (if s then [126w] else []) in
    let (rest,c) = mw_to_dec xs in
      (sign ++ rest,c)`

val mw_to_dec_thm = store_thm("mw_to_dec_thm",
  ``!(xs:'a word list).
      10 < dimword (:'a) ==>
      (mw_to_dec xs = (MAP (n2w o ORD) (num_to_dec_string (mw2n xs)),T))``,
  STRIP_TAC \\ STRIP_ASSUME_TAC (SPEC_ALL k2mw_EXISTS)
  \\ Q.PAT_X_ASSUM `xs = bb` (fn th => ONCE_REWRITE_TAC [th])
  \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`xs`,`xs`)
  \\ completeInduct_on `k` \\ ONCE_REWRITE_TAC [mw_to_dec_def]
  \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS,LET_DEF] \\ STRIP_TAC
  \\ `?x1 x2 x3. mw_simple_div 0x0w (REVERSE (k2mw (LENGTH (xs:'a word list)) k)) 0xAw = (x1,x2:'a word,x3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ `0x0w <+ 10w` by FULL_SIMP_TAC (srw_ss()) [WORD_LO]
  \\ IMP_RES_TAC mw_simple_div_thm
  \\ FULL_SIMP_TAC std_ss [REVERSE_REVERSE]
  \\ IMP_RES_TAC mw2n_k2mw \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
  \\ Q.PAT_X_ASSUM `10 < dimword (:'a)` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL,AND_IMP_INTRO]
  \\ FULL_SIMP_TAC std_ss [mw_fix_LENGTH_ZERO]
  \\ ONCE_REWRITE_TAC [num_to_dec_string_unroll]
  \\ `(k DIV 10 = 0) = k < 10` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [DIV_EQ_X,NOT_LESS]
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `k < 10` \\ FULL_SIMP_TAC std_ss [] THEN1
   (EVAL_TAC \\ `48 + k < 256` by DECIDE_TAC
    \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [SNOC,MAP,word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ Q.PAT_X_ASSUM `!m. bbb` (MP_TAC o Q.SPECL [`k DIV 10`,`(mw_fix (REVERSE x1))`])
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [DIV_LT_X,NOT_LESS]
    \\ `0 < dimwords (LENGTH x1) (:'a)` by FULL_SIMP_TAC std_ss [ZERO_LT_dimwords]
    \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ MP_TAC (Q.SPEC `(mw_fix (REVERSE x1))` mw2n_lt)
    \\ FULL_SIMP_TAC std_ss [mw2n_mw_fix,DIV_LT_X])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `(k2mw (LENGTH (mw_fix (REVERSE x1))) (k DIV 10)) =
      (mw_fix (REVERSE x1))` by ALL_TAC THEN1
   (MP_TAC (Q.SPEC `mw_fix (REVERSE x1)` k2mw_mw2n)
    \\ FULL_SIMP_TAC std_ss [mw2n_mw_fix])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [mw2n_mw_fix]
  \\ FULL_SIMP_TAC (srw_ss()) [word_add_n2w]
  \\ `k MOD 10 < 10` by FULL_SIMP_TAC (srw_ss()) []
  \\ `48 + k MOD 10 < 256` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]);

val mwi_to_dec_thm = store_thm("mwi_to_dec_thm",
  ``10 < dimword (:'a) /\ ((xs = []) ==> ~s) /\ mw_ok xs ==>
    (mwi_to_dec (s,xs:'a word list) =
        (MAP (n2w o ORD) (int_to_str (mw2i (s,xs))),T))``,
  SIMP_TAC std_ss [mwi_to_dec_def,int_to_str_def,i2mw_def,LET_DEF] \\ STRIP_TAC
  \\ `mw2i (s,xs) < 0 <=> s` by ALL_TAC THEN1
   (Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
    \\ Cases_on `s` \\ SIMP_TAC std_ss [mw2i_def]
    \\ `mw2n xs <> 0` by
      (ASM_SIMP_TAC std_ss [GSYM mw_fix_NIL,mw_ok_mw_fix_ID])
    \\ intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC mw_to_dec_thm
  \\ FULL_SIMP_TAC std_ss []
  \\ `Num (ABS (mw2i (s,xs))) = mw2n xs` by ALL_TAC THEN1
   (Cases_on `s` \\ SIMP_TAC std_ss [mw2i_def] \\ intLib.COOPER_TAC)
  \\ Cases_on `s` \\ FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,APPEND,mw2n_n2mw,CONS_11]
  \\ EVAL_TAC);


(* top-level entry point *)

val _ = Hol_datatype `mw_op = Add | Sub | Mul | Div | Mod | Lt | Eq | Dec`;

val int_op_def = Define `
  (int_op Add i j = i + j) /\
  (int_op Sub i j = i - j) /\
  (int_op Mul i j = i * j) /\
  (int_op Div i j = i / j) /\
  (int_op Mod i j = i % j) /\
  (int_op Lt i j = if i < j then 1 else 0) /\
  (int_op Eq i j = if i = j then 1 else 0:int) /\
  (int_op Dec i j = 0)`; (* decimal representation returned separately *)

val mwi_op_def = Define `
  (mwi_op Add s_xs t_ys = mwi_add s_xs t_ys) /\
  (mwi_op Sub s_xs t_ys = mwi_sub s_xs t_ys) /\
  (mwi_op Mul s_xs t_ys = mwi_mul s_xs t_ys) /\
  (mwi_op Div s_xs t_ys = mwi_div s_xs t_ys) /\
  (mwi_op Mod s_xs t_ys = mwi_mod s_xs t_ys) /\
  (mwi_op Lt s_xs t_ys = i2mw (if mwi_lt s_xs t_ys then 1 else 0)) /\
  (mwi_op Eq s_xs t_ys = i2mw (if mwi_eq s_xs t_ys then 1 else 0)) /\
  (mwi_op Dec s_xs t_ys = (F,[]))`;

val mwi_op_thm = Q.store_thm("mwi_op_thm",
  `!op i j.
      ((op = Div) \/ (op = Mod) ==> j <> 0) ==>
      (mwi_op op (i2mw i) (i2mw j) = i2mw (int_op op i j))`,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [int_op_def,mwi_op_def,
    mwi_add_thm,mwi_sub_thm,mwi_mul_thm,mwi_divmod_thm,mwi_lt_def,
    mwi_eq_def,mwi_compare_thm,mwi_div_def,mwi_mod_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [EVAL ``i2mw 0``]
  \\ Cases_on `i < j` \\ FULL_SIMP_TAC std_ss []
  \\ `i <> j` by intLib.COOPER_TAC \\ FULL_SIMP_TAC std_ss []);


(* extra *)

val LESS_EQ_LENGTH = Q.store_thm("LESS_EQ_LENGTH",
  `!xs n. n <= LENGTH xs ==> ?xs1 xs2. (xs = xs1 ++ xs2) /\ (LENGTH xs1 = n)`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_NIL]
  \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::xs1`,`xs2`] \\ FULL_SIMP_TAC (srw_ss()) []);

val LENGTH_mw_add = store_thm("LENGTH_mw_add",
  ``!xs1 ys c qs1 c1. (mw_add xs1 ys c = (qs1,c1)) ==> (LENGTH xs1 = LENGTH qs1)``,
  Induct \\ FULL_SIMP_TAC std_ss [mw_add_def,LET_DEF,single_add_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `t = (dimword (:'a) <= w2n h + w2n (HD ys) + b2n c)`
  \\ `?x1 x2. mw_add xs1 (TL ys) t = (x1,x2)` by METIS_TAC [PAIR]
  \\ RES_TAC \\ Cases_on `qs1` \\ FULL_SIMP_TAC (srw_ss()) []);

val LENGTH_mw_fix_IMP = Q.store_thm("LENGTH_mw_fix_IMP",
  `(LENGTH xs = LENGTH ys) ==>
    LENGTH (mw_fix xs) <= LENGTH ys`,
  METIS_TAC [LENGTH_mw_fix]);

val LENGTH_mw_subv = Q.store_thm("LENGTH_mw_subv",
  `!ys xs. LENGTH xs <= LENGTH ys ==> (LENGTH (mw_subv ys xs) <= LENGTH ys)`,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [mw_subv_def,LET_DEF]
  \\ MATCH_MP_TAC LENGTH_mw_fix_IMP \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ Cases_on `mw_sub ys xs T`
  \\ IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss []);

val mw_add_F = store_thm("mw_add_F",
  ``!xs2. (mw_add xs2 (MAP (\x. 0x0w) xs2) F = (xs2,F))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [mw_add_def,MAP,single_add_def,
    LET_DEF,b2w_def,b2n_def,GSYM NOT_LESS,w2n_lt]);

val LENGTH_mw_addv = Q.store_thm("LENGTH_mw_addv",
  `LENGTH ys <= LENGTH xs ==>
    LENGTH (mw_addv xs ys F) <= LENGTH xs + LENGTH ys`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss [mw_addv_EQ_mw_add,LET_DEF]
  \\ `?ts1 t1. mw_add xs1 ys F = (ts1,t1)` by METIS_TAC [PAIR]
  \\ `?ts2 t2. mw_add xs2 (MAP (\x. 0x0w) xs2) t1 = (ts2,t2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `xs1` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,mw_add_def]
    \\ Cases_on `t1` \\ FULL_SIMP_TAC std_ss [mw_add_F,LENGTH_APPEND]
    \\ Cases_on `ts1` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH])
  \\ IMP_RES_TAC LENGTH_mw_add
  \\ Cases_on `t2` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC);

val LENGTH_mw_mul = Q.store_thm("LENGTH_mw_mul",
  `!xs ys zs.
      (LENGTH zs = LENGTH ys) ==>
      (LENGTH (mw_mul xs ys zs) = LENGTH xs + LENGTH ys)`,
  Induct \\ FULL_SIMP_TAC std_ss [mw_mul_def,LENGTH,LET_DEF]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH (mw_mul_pass h ys zs 0w) = LENGTH ys + 1` by
       FULL_SIMP_TAC std_ss [LENGTH_mw_mul_pass]
  \\ Cases_on `mw_mul_pass h ys zs 0x0w`
  \\ FULL_SIMP_TAC std_ss [LENGTH,TL,ADD1] \\ DECIDE_TAC);

val LESS_EQ_LENGTH_ALT = Q.store_thm("LESS_EQ_LENGTH_ALT",
  `!xs n. n <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys2 = n)`,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND_NIL,LENGTH_SNOC]
  \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND_NIL]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC]
  \\ Q.LIST_EXISTS_TAC [`ys1`,`SNOC x ys2`]
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,SNOC_APPEND]);

val LENGTH_mw_div_aux = store_thm("LENGTH_mw_div_aux",
  ``!ts1 ts2 ys qs rs.
      (mw_div_aux ts1 ts2 ys = (qs,rs)) /\ (LENGTH ts2 = LENGTH ys) ==>
      (LENGTH rs = LENGTH ys) /\ (LENGTH qs = LENGTH ts1)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC
  THEN1 (SIMP_TAC std_ss [Once mw_div_aux_def])
  \\ NTAC 7 STRIP_TAC
  \\ SIMP_TAC std_ss [Once mw_div_aux_def,NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `q = (mw_div_adjust
                     (mw_div_guess (REVERSE (x::ts2)) (REVERSE ys))
                     (x::ts2) ys)`
  \\ Cases_on `mw_sub (x::ts2) (mw_mul_by_single q ys) T`
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_mw_sub
  \\ `(q' = []) \/ ?y ys2. q' = SNOC y ys2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_SNOC,FRONT_SNOC]
  \\ Cases_on `mw_div_aux ts1 ys2 ys` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ METIS_TAC []);


(* combined mul_by_single *)

val mw_mul_by_single2_def = Define `
  (mw_mul_by_single2 x1 x2 [] k1 k2 = [k2]) /\
  (mw_mul_by_single2 x1 x2 (y::ys) k1 k2 =
     let (y1,k1) = single_mul_add x1 y k1 0w in
     let (y2,k2) = single_mul_add x2 y1 k2 0w in
       y2 :: mw_mul_by_single2 x1 x2 ys k1 k2)`;

val k2mw_SUC_0 = Q.prove(
  `k2mw (SUC n) 0 = 0w :: k2mw n 0`,
  SRW_TAC [] [k2mw_def,ZERO_DIV]);

val mw_mul_pass_NOT_NIL = Q.prove(
  `!xs ys r x. mw_mul_pass x xs ys r <> []`,
  Cases \\ SIMP_TAC (srw_ss()) [mw_mul_pass_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ SIMP_TAC (srw_ss()) []);

val mw_mul_by_single2_thm = Q.prove(
  `!ys x1 x2 k1 k2.
      mw_mul_by_single2 x1 x2 ys k1 k2 =
        let ys = mw_mul_pass x1 ys (k2mw (LENGTH ys) 0) k1 in
        let ys = mw_mul_pass x2 (FRONT ys) (k2mw (LENGTH (FRONT ys)) 0) k2 in
          ys`,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [mw_mul_pass_def,LENGTH,k2mw_SUC_0]
  \\ FULL_SIMP_TAC std_ss [mw_mul_by_single2_def,LET_DEF]
  \\ Cases_on `single_mul_add x1 h k1 0x0w`
  \\ FULL_SIMP_TAC (srw_ss()) [FRONT_DEF,mw_mul_pass_NOT_NIL]
  \\ SIMP_TAC (srw_ss()) [mw_mul_pass_def,LENGTH,k2mw_SUC_0,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ SIMP_TAC std_ss []) |> Q.SPECL [`ys`,`x1`,`x2`,`0w`,`0w`]
  |> SIMP_RULE std_ss [GSYM mw_mul_by_single_def,LET_DEF];

val _ = save_thm("mw_mul_by_single2_thm",mw_mul_by_single2_thm);

(* calc only top three results of mw_mul_pass *)

val mw_mul_pass_top_def = Define `
  (mw_mul_pass_top x [] (k,k1,k2) = (k,k1,k2)) /\
  (mw_mul_pass_top x (y::ys) (k,k1,k2) =
     let (y1,k) = single_mul_add x y k 0w in
       mw_mul_pass_top x ys (k,y1,k1))`;

val k2mw_LENGTH_0 = Q.store_thm("k2mw_LENGTH_0",
  `!ys. (k2mw (LENGTH ys) 0) = MAP (K 0w) ys`,
  Induct \\ EVAL_TAC \\
  SIMP_TAC std_ss [LEN_LENGTH_LEM,GSYM ADD1,k2mw_def] \\
  FULL_SIMP_TAC std_ss [MATCH_MP ZERO_DIV ZERO_LT_dimword]);

val mw_mul_pass_top_lemma = prove(
  ``!ys k1 k2 k3 x.
      ((let (x1,x2,x3) = mw_mul_pass_top x ys (k1,k2,k3) in [x1;x2;x3]) =
       TAKE 3 (REVERSE (mw_mul_pass x ys (MAP (K 0w) ys) k1) ++ [k2;k3]))``,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [mw_mul_pass_def,mw_mul_pass_top_def]
  \\ FULL_SIMP_TAC std_ss [HD,MAP,TL] \\ REPEAT STRIP_TAC
  \\ Cases_on `single_mul_add x h k1 0x0w`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,REVERSE_DEF,GSYM APPEND_ASSOC,APPEND]
  \\ Cases_on `REVERSE (mw_mul_pass x ys (MAP (K 0x0w) ys) r)` THEN1
   (FULL_SIMP_TAC std_ss [REVERSE_EQ_NIL]
    \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_mw_mul_pass])
  \\ Cases_on `t` \\ EVAL_TAC \\ Cases_on `t'` \\ EVAL_TAC)
  |> Q.SPECL [`ys`,`0w`] |> GEN_ALL
  |> SIMP_RULE std_ss [GSYM k2mw_LENGTH_0,GSYM mw_mul_by_single_def];

val mw_mul_pass_top_thm = store_thm("mw_mul_pass_top_thm",
  ``1 < LENGTH ys ==>
    (mw_mul_pass_top x ys (0w,0w,0w) =
      (LAST (mw_mul_by_single x ys),
       LAST (BUTLAST (mw_mul_by_single x ys)),
       LAST (BUTLAST (BUTLAST (mw_mul_by_single x ys)))))``,
  STRIP_TAC
  \\ ASSUME_TAC (mw_mul_pass_top_lemma |> Q.SPECL [`ys`,`0w`,`0w`,`x`])
  \\ Cases_on `mw_mul_pass_top x ys (0x0w,0x0w,0x0w)`
  \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `2 < LENGTH (mw_mul_by_single x ys)` by
       (FULL_SIMP_TAC std_ss [LENGTH_mw_mul_by_single] \\ DECIDE_TAC)
  \\ `(mw_mul_by_single x ys = []) \/
      ?y ys2. mw_mul_by_single x ys = SNOC y ys2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_SNOC,ADD1]
  \\ `(ys2 = []) \/ ?y3 ys3. ys2 = SNOC y3 ys3` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_SNOC,ADD1]
  \\ `(ys3 = []) \/ ?y4 ys4. ys3 = SNOC y4 ys4` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_SNOC,ADD1]
  \\ FULL_SIMP_TAC bool_ss [REVERSE_SNOC,TAKE,LAST_SNOC,FRONT_SNOC,
        DECIDE ``3 = SUC (SUC (SUC 0))``,APPEND,CONS_11]);

(* extra lemmas about mw_addv special case *)

val single_add_lemma = prove(
  ``!h. single_add h 0x0w F = (h,F)``,
  Cases \\ FULL_SIMP_TAC std_ss [single_add_def,word_add_n2w,b2w_def,
     b2n_def,w2n_n2w,ZERO_LT_dimword,GSYM NOT_LESS]);

val mw_addv_NIL_F = Q.prove(
  `!xs. mw_addv xs [] F = xs`,
  Induct THEN1 EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [mw_addv_def,LET_DEF,single_add_lemma,CONS_11]);

val mw_addv_CONS_NIL_T = Q.prove(
  `mw_addv (x::xs) [] T =
      if x = ~0w:word64 then 0w::mw_addv xs [] T else (x+1w)::xs`,
  Cases_on `x = ~0x0w`
  \\ ASM_SIMP_TAC std_ss [mw_addv_def,LET_DEF,
       EVAL ``single_add (~0x0w) (0x0w:word64) T``]
  \\ `single_add x 0x0w T = (x+1w,F)` by ALL_TAC THEN1
   (Cases_on `x` \\ FULL_SIMP_TAC std_ss [single_add_def,word_add_n2w,b2w_def,
      b2n_def,w2n_n2w,ZERO_LT_dimword,GSYM NOT_LESS,n2w_11,EVAL ``~0w:word64``,
      EVAL ``dimword (:64)``] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [mw_addv_NIL_F]);

val mw_addv_NIL = save_thm("mw_addv_NIL",LIST_CONJ
  [EVAL ``mw_addv [] [] T``,mw_addv_NIL_F,GEN_ALL mw_addv_CONS_NIL_T]);


(* verify implementation for single_div (to be used on arch without div) *)

val num_div_loop_def = Define `
  num_div_loop (k:num,n:num,m:num,i:num) =
    if k = 0 then (m,i) else
      let n = n DIV 2 in
      let m = m * 2 in
        if i < n then
          num_div_loop (k-1,n,m,i)
        else
          num_div_loop (k-1,n,m+1,i-n)`

val num_div_loop_lemma = prove(
  ``!k i n m.
      i < n * 2 ** k /\ 0 < n ==>
      (num_div_loop (k,n * 2 ** k,m,i) = (m * 2 ** k + i DIV n,i MOD n))``,
  Induct
  \\ simp [Once num_div_loop_def,arithmeticTheory.LESS_DIV_EQ_ZERO]
  \\ rw [] \\ fs [EXP,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ fs [RIGHT_ADD_DISTRIB,MOD_SUB,DIV_SUB]
  \\ qsuff_tac `2 ** k <= i DIV n` THEN1 decide_tac
  \\ fs [X_LE_DIV]);

val num_div_loop_thm = save_thm("num_div_loop_thm",
  num_div_loop_lemma
  |> Q.SPECL [`k`,`i`,`n`,`0`] |> SIMP_RULE std_ss []);

val single_div_loop_def = Define `
  single_div_loop (k:'a word,ns:'a word list,m:'a word,is:'a word list) =
    if k = 0w then (m,is) else
      let ns = mw_shift ns in
      let m = m << 1 in
        if mw_cmp is ns = SOME T then
          single_div_loop (k-1w,ns,m,is)
        else
          let m = m + 1w in
          let (is,_) = mw_sub is ns T in
            single_div_loop (k-1w,ns,m,is)`

val single_div_full_def = Define `
  single_div_full m2 (m1:'a word) n =
    let (m,is) = single_div_loop (n2w (dimindex (:'a)),[0w;n],0w,[m1;m2]) in
      (m, HD is)`;

fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

val impl_tac = match_mp_tac IMP_IMP \\ conj_tac

val single_div_loop_thm = prove(
  ``!k ns m is t qs.
      (single_div_loop (n2w k,ns,m,is) = (t,qs:'a word list)) /\
      k < dimword (:'a) /\
      k <= dimindex (:'a) /\ (w2n m < 2 ** (dimindex (:'a) - k)) /\
      (LENGTH ns = 2) /\ (LENGTH is = 2) ==>
      (num_div_loop (k,mw2n ns,w2n m,mw2n is) = (w2n t, mw2n qs)) /\
      (LENGTH qs = 2)``,
  Induct THEN1 (fs [Once num_div_loop_def,Once single_div_loop_def])
  \\ NTAC 6 strip_tac
  \\ qpat_x_assum `single_div_loop _ = _` mp_tac
  \\ once_rewrite_tac [single_div_loop_def,num_div_loop_def]
  \\ fs [mw_shift_thm,LENGTH_mw_shift,mw_cmp_thm]
  \\ Cases_on `mw2n is < mw2n ns DIV 2` \\ fs []
  THEN1
   (fs [ADD1,GSYM word_add_n2w] \\ strip_tac
    \\ first_x_assum drule
    \\ fs [LENGTH_mw_shift,mw_shift_thm]
    \\ impl_tac
    THEN1
      (Cases_on `m` \\ fs [WORD_MUL_LSL,word_mul_n2w]
       \\ `2 * n < dimword (:'a)` by
        (fs [LESS_EQ_EXISTS] \\ rfs [dimword_def,EXP_ADD]
         \\ Cases_on `2 ** k` \\ fs []
         \\ Cases_on `n'` \\ fs [MULT_CLAUSES])
       \\ fs [LESS_EQ_EXISTS] \\ rfs []
       \\ fs [EXP,GSYM ADD1])
    \\ `w2n (m << 1) = 2 * w2n m` by all_tac \\ fs []
    \\ Cases_on `m` \\ fs [WORD_MUL_LSL,word_mul_n2w]
    \\ fs [LESS_EQ_EXISTS] \\ rfs [dimword_def]
    \\ fs [EXP,GSYM ADD1,ADD_CLAUSES,EXP_ADD]
    \\ Cases_on `2 ** k` \\ fs []
    \\ Cases_on `n'` \\ fs [MULT_CLAUSES])
  \\ fs [] \\ Cases_on `(mw_sub is (mw_shift ns) T)` \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w]
  \\ strip_tac
  \\ first_x_assum drule
  \\ fs [LENGTH_mw_shift,mw_shift_thm]
  \\ impl_tac THEN1
   (imp_res_tac LENGTH_mw_sub \\ fs [LENGTH_mw_shift]
    \\ Cases_on `m` \\ fs [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ fs [LESS_EQ_EXISTS] \\ rfs [dimword_def,EXP_ADD]
    \\ `2 * n + 1 < 2 * (2 ** k * 2 ** p) /\
        2 * n + 1 < 2 * 2 ** p` by all_tac \\ fs []
    \\ Cases_on `2 ** k` \\ fs []
    \\ Cases_on `n'` \\ fs [MULT_CLAUSES])
  \\ `w2n (m << 1 + 1w) = 2 * w2n m + 1` by all_tac \\ fs []
  THEN1
   (Cases_on `m` \\ fs [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ fs [LESS_EQ_EXISTS] \\ rfs [dimword_def,EXP_ADD]
    \\ Cases_on `2 ** k` \\ fs []
    \\ Cases_on `n'` \\ fs [MULT_CLAUSES])
  \\ `mw2n q = mw2n is - mw2n ns DIV 2` by all_tac \\ fs []
  \\ `q = FST (mw_sub is (mw_shift ns) T)` by fs []
  \\ pop_assum (fn th => fs [th])
  \\ fs [GSYM mw_shift_thm]
  \\ match_mp_tac mw_sub_thm
  \\ fs [LENGTH_mw_shift]);

val mw2n_0 = Q.store_thm("mw2n_0",
  `(mw2n [] = 0) /\
    (mw2n (0w::xs:'a word list) = dimword (:'a) * mw2n xs)`,
  fs [mw2n_def]);

val HD_eq_n2w_mw2n = Q.store_thm("HD_eq_n2w_mw2n",
  `LENGTH xs <> 0 /\ mw2n xs < dimword (:'a) ==>
    (HD xs = n2w (mw2n (xs:'a word list)))`,
  Cases_on `xs` \\ fs [mw2n_def]
  \\ Cases_on `mw2n t` \\ fs []
  \\ fs [MULT_CLAUSES]);

val LESS_2_EXP = Q.store_thm("LESS_2_EXP[simp]",
  `!n. n < 2 ** n`,
  Induct \\ fs [EXP]);

val single_div_full_thm = Q.store_thm("single_div_full_thm",
  `mw2n [x2;x1] < mw2n [0w;y] ==>
    (single_div_full x1 x2 y = single_div x1 x2 y)`,
  fs [single_div_full_def]
  \\ Cases_on `single_div_loop (n2w (dimindex (:'a)),[0w; y],0w,[x2; x1])`
  \\ fs [] \\ strip_tac
  \\ drule single_div_loop_thm \\ impl_tac
  THEN1 (fs [] \\ fs [dimword_def,LESS_2_EXP])
  \\ rw [] \\ fs [mw2n_0]
  \\ `y <> 0w` by (Cases_on `y` \\ fs [mw2n_def] \\ CCONTR_TAC \\ fs [])
  \\ `0 < mw2n [0w; y]` by fs [mw2n_0]
  \\ fs [dimword_def]
  \\ imp_res_tac num_div_loop_thm
  \\ pop_assum kall_tac
  \\ `0 < mw2n [y]` by (fs [mw2n_0,mw2n_def] \\ Cases_on `y` \\ fs [])
  \\ fs [] \\ fs [single_div_def]
  \\ Cases_on `x2` \\ Cases_on `x1` \\ Cases_on `y` \\ fs [mw2n_def]
  \\ rw [] \\ match_mp_tac HD_eq_n2w_mw2n \\ fs []
  \\ rpt (qpat_assum `_ = mw2n _` (fn th => fs [GSYM th]))
  \\ fs [DIV_LT_X] \\ fs [dimword_def]
  \\ match_mp_tac LESS_TRANS
  \\ rename1 `k < 2 ** dimindex (:'a)`
  \\ qexists_tac `k` \\ fs []);

val _ = export_theory();
