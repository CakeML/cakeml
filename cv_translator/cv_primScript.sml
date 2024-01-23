(*
  Prove theorems cv_transLib uses for its operation
*)
open HolKernel Parse boolLib bossLib;
open cv_typeTheory cvTheory cv_typeLib cv_repLib;
open arithmeticTheory wordsTheory cv_repTheory integerTheory;

val _ = new_theory "cv_prim";

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(*----------------------------------------------------------*
   bool
 *----------------------------------------------------------*)

Theorem cv_rep_T[cv_rep]:
  b2c T = Num 1
Proof
  fs []
QED

Theorem cv_rep_F[cv_rep]:
  b2c F = Num 0
Proof
  fs []
QED

Theorem cv_rep_not[cv_rep]:
  b2c (~b1) = cv_sub (Num 1) (b2c b1)
Proof
  Cases_on ‘b1’ \\ fs []
QED

Theorem cv_rep_and[cv_rep]:
  b2c (b1 ∧ b2) = cv_if (b2c b1) (b2c b2) (Num 0)
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ fs []
QED

Theorem cv_rep_or[cv_rep]:
  b2c (b1 ∨ b2) = cv_if (b2c b1) (Num 1) (b2c b2)
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ fs [cv_rep_def]
QED

(*----------------------------------------------------------*
   num
 *----------------------------------------------------------*)

Theorem cv_rep_suc[cv_rep]:
  Num (SUC n) = cv_add (Num n) (Num 1)
Proof
  fs []
QED

Theorem cv_rep_sub1[cv_rep]:
  Num (PRE n) = cv_sub (Num n) (Num 1)
Proof
  fs []
QED

Theorem cv_rep_add[cv_rep]:
  Num (n + m) = cv_add (Num n) (Num m)
Proof
  fs []
QED

Theorem cv_rep_sub[cv_rep]:
  Num (n - m) = cv_sub (Num n) (Num m)
Proof
  fs []
QED

Theorem cv_rep_mul[cv_rep]:
  Num (n * m) = cv_mul (Num n) (Num m)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_div[cv_rep]:
  Num (n DIV m) = cv_div (Num n) (Num m)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_mod[cv_rep]:
  Num (n MOD m) = cv_mod (Num n) (Num m)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_exp[cv_rep]:
  Num (n ** m) = cv_exp (Num n) (Num m)
Proof
  fs [cv_rep_def,cvTheory.cv_exp_def]
QED

Theorem cv_rep_odd[cv_rep]:
  b2c (ODD n) = cv_mod (Num n) (Num 2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [bitTheory.ODD_MOD2_LEM]
  \\ ‘n MOD 2 < 2’ by fs []
  \\ Cases_on ‘n MOD 2’ \\ fs []
QED

Theorem cv_rep_even[cv_rep]:
  b2c (EVEN n) = cv_sub (Num 1) (cv_mod (Num n) (Num 2))
Proof
  simp [cv_rep_odd,cv_rep_not,arithmeticTheory.EVEN_ODD]
QED

Theorem cv_rep_lt[cv_rep]:
  b2c (n < m) = cv_lt (Num n) (Num m)
Proof
  fs [cv_rep_def] \\ rw []
QED

Theorem cv_rep_num_case[cv_rep]:
  cv_rep p1 c1 Num x ∧
  cv_rep p2 c2 (a:'a->cv) y ∧
  (∀v:num. cv_rep (p3 v) (c3 (Num v)) (a:'a->cv) (z v)) ⇒
  cv_rep (p1 ∧ p2 ∧ ∀n. x = SUC n ⇒ p3 n)
         (cv_if (cv_lt (Num 0) c1) (let y = cv_sub c1 (Num 1) in c3 y) c2)
         a (num_CASE x y z)
Proof
  rw [] \\ gvs [cv_rep_def] \\ rw [] \\ gvs []
  \\ Cases_on ‘x’ \\ gvs []
QED

Definition cv_min_def:
  cv_min x y = cv_if (cv_lt x y) x y
End

Definition cv_max_def:
  cv_max x y = cv_if (cv_lt x y) y x
End

Theorem cv_min_thm[cv_rep]:
  Num (MIN m n) = cv_min (Num m) (Num n)
Proof
  fs [cv_min_def] \\ rw []
  \\ BasicProvers.every_case_tac \\ fs []
  \\ gvs [arithmeticTheory.MIN_DEF]
QED

Theorem cv_max_thm[cv_rep]:
  Num (MAX m n) = cv_max (Num m) (Num n)
Proof
  fs [cv_max_def] \\ rw []
  \\ BasicProvers.every_case_tac \\ fs []
  \\ gvs [arithmeticTheory.MAX_DEF]
QED


(*----------------------------------------------------------*
   int
 *----------------------------------------------------------*)

Theorem cv_int_of_num[cv_rep]:
  from_int (&n) = Num n
Proof
  gvs[from_int_def]
QED

Definition cv_abs_def:
  cv_abs i = cv_if (cv_ispair i) (cv_fst i) i
End

Theorem cv_Num[cv_rep]:
  Num (integer$Num i) = cv_abs (from_int i)
Proof
  gvs[from_int_def, cv_abs_def] >>
  rw[] >> gvs[cv_ispair_def]
QED

(*----------------------------------------------------------*
   char
 *----------------------------------------------------------*)

Theorem cv_chr_thm[cv_rep]:
  n < 256 ⇒ from_char (CHR n) = Num n
Proof
  gvs [from_char_def]
QED

Theorem cv_ord_thm[cv_rep]:
  Num (ORD c) = from_char c
Proof
  gvs [from_char_def]
QED

(*----------------------------------------------------------*
   if, let, arb, =
 *----------------------------------------------------------*)

Theorem cv_rep_if[cv_rep]:
  cv_rep p1 c1 b2c b ∧
  cv_rep p2 c2 f t ∧
  cv_rep p3 c3 f e ⇒
  cv_rep (p1 ∧ (b ⇒ p2) ∧ (~b ⇒ p3))
         (cv_if c1 c2 c3) f (if b then t else e)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs []
QED

Theorem cv_rep_let[cv_rep]:
  cv_rep p1 c1 (a:'a->cv) x ∧
  (∀v. cv_rep (p2 v) (c2 (a v)) (b:'b->cv) (y v)) ⇒
  cv_rep (p1 ∧ ∀v. v = x ⇒ p2 v) (LET c2 c1) b (LET y x)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_arb[cv_rep]:
  F ⇒ f ARB = Num 0
Proof
  fs []
QED

Theorem cv_rep_eq[cv_rep]:
  cv_rep p1 c1 f x ∧
  cv_rep p2 c2 f y ∧
  from_to f t ⇒
  cv_rep (p1 ∧ p2) (cv_eq c1 c2) b2c (x = y)
Proof
  fs [cv_rep_def,cv_eq_def]
  \\ Cases_on ‘x = y’ \\ fs []
  \\ rw [] \\ gvs []
  \\ fs [from_to_def]
  \\ metis_tac []
QED

(*----------------------------------------------------------*
   word conversions
 *----------------------------------------------------------*)

Theorem cv_rep_word_w2n[cv_rep]:
  Num (w2n w) = from_word (w :'a word)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
QED

Theorem cv_rep_word_n2w[cv_rep]:
  from_word (n2w n : 'a word) = (cv_mod (Num n) (Num (2 ** dimindex (:'a))))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def,dimword_def]
QED

Theorem cv_rep_word_w2w[cv_rep]:
  from_word ((w2w (w:'a word)) : 'b word)
  =
  if dimindex (:'a) ≤ dimindex (:'b) then from_word w else
    cv_mod (from_word w) (Num (2 ** dimindex (:'b)))
Proof
  fs [cv_rep_def] \\ rw []
  \\ gvs [from_word_def,GSYM dimword_def,w2w_def]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt
  \\ gvs [dimword_def]
QED

(*----------------------------------------------------------*
   word arithmetic
 *----------------------------------------------------------*)

Theorem cv_rep_word_add[cv_rep]:
  from_word (w1 + w2)
  =
  cv_mod (cv_add (from_word (w1 :'a word)) (from_word w2)) (Num (dimword (:'a)))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [wordsTheory.word_add_n2w]
QED

Definition cv_word_sub_def:
  cv_word_sub x y d =
    cv_if (cv_lt x y)
      (cv_sub (cv_add x d) y)
      (cv_sub x y)
End

Theorem cv_rep_word_sub[cv_rep]:
  from_word (w1 - w2 :'a word)
  =
  cv_word_sub (from_word w1) (from_word w2) (Num (dimword (:'a)))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def,cv_word_sub_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ reverse $ Cases_on ‘n < n'’ \\ gvs []
  >- gvs [arithmeticTheory.NOT_LESS,GSYM wordsTheory.n2w_sub]
  \\ gvs [wordsTheory.word_sub_def,wordsTheory.word_2comp_n2w]
  \\ gvs [wordsTheory.word_add_n2w]
QED

Theorem cv_rep_word_neg[cv_rep]:
  from_word (- w1 :'a word)
  =
  cv_word_sub (Num 0) (from_word w1) (Num (dimword (:'a)))
Proof
  rewrite_tac [GSYM wordsTheory.WORD_SUB_LZERO,cv_rep_word_sub]
  \\ fs [from_word_def]
QED

Theorem cv_rep_word_mul[cv_rep]:
  from_word (w1 * w2 :'a word)
  =
  cv_mod (cv_mul (from_word w1) (from_word w2)) (Num (dimword (:'a)))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [wordsTheory.word_mul_n2w]
QED

Theorem cv_rep_word_div[cv_rep]:
  from_word (word_div w1 w2)
  =
  cv_div (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [word_div_def]
  \\ rename [‘n DIV m’] \\ Cases_on ‘m’ \\ fs []
  \\ gvs [DIV_LT_X] \\ gvs [MULT_CLAUSES]
QED

Theorem cv_rep_word_mod[cv_rep]:
  from_word (word_mod w1 w2)
  =
  cv_mod (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [word_mod_def]
  \\ rename [‘n MOD m’] \\ Cases_on ‘m’ \\ fs []
  \\ irule LESS_EQ_LESS_TRANS
  \\ last_x_assum $ irule_at Any
  \\ irule arithmeticTheory.MOD_LESS_EQ \\ fs []
QED

(*----------------------------------------------------------*
   word_msb, unit_max, word shifts
 *----------------------------------------------------------*)

Theorem cv_rep_word_msb[cv_rep]:
  b2c (word_msb w)
  =
  cv_div (from_word (w :'a word)) (Num (2 ** (dimindex (:'a) - 1)))
Proof
  rw [Once EQ_SYM_EQ] \\ gvs [from_word_def]
  \\ Cases_on ‘w’ \\ gvs [wordsTheory.word_msb_def]
  \\ gvs [wordsTheory.n2w_def,fcpTheory.FCP_BETA,bitTheory.BIT_def,
          bitTheory.BITS_THM,wordsTheory.dimword_def]
  \\ ‘0 < dimindex (:'a)’ by fs [fcpTheory.DIMINDEX_GT_0]
  \\ Cases_on ‘dimindex (:'a)’ \\ gvs []
  \\ rename [‘SUC l’]
  \\ ‘0 < 2:num’ by fs []
  \\ drule arithmeticTheory.DIVISION
  \\ disch_then $ qspec_then ‘n DIV (2 ** l)’
       (strip_assume_tac o ONCE_REWRITE_RULE [CONJ_COMM])
  \\ pop_assum (fn th => simp [Once th])
  \\ simp [arithmeticTheory.DIV_DIV_DIV_MULT]
  \\ ‘n DIV (2 * 2 ** l) = 0’ by gvs [DIV_EQ_X,GSYM EXP]
  \\ asm_rewrite_tac [] \\ simp []
  \\ drule (DECIDE “n < 2 ⇒ n = 0 ∨ n = 1:num”)
  \\ strip_tac \\ gvs []
QED

Theorem cv_rep_word_uint_max[cv_rep]:
  from_word (UINT_MAXw:'a word)
  =
  Num (2 ** dimindex (:'a) - 1)
Proof
  rw [cv_rep_def,from_word_def] \\ EVAL_TAC
  \\ gvs [w2n_n2w,dimword_def]
QED

Theorem cv_rep_word_lsl[cv_rep]:
  from_word (word_lsl (w:'a word) n)
  =
  cv_mod (cv_mul (from_word w) (cv_exp (Num 2) (Num n)))
         (Num (2 ** dimindex (:'a)))
Proof
  gvs [cv_rep_def] \\ rw [] \\ gvs []
  \\ gvs [from_word_def,cv_exp_def]
  \\ Cases_on ‘w’ \\ gvs [word_lsl_n2w]
  \\ rw [] \\ gvs [dimword_def]
  \\ ‘0n < 2 ** dimindex (:'a)’ by gvs []
  \\ drule MOD_TIMES2
  \\ disch_then (fn th => once_rewrite_tac [GSYM th])
  \\ qsuff_tac ‘2 ** n MOD 2 ** dimindex (:α) = 0’ \\ gvs []
  \\ ‘dimindex (:'a) ≤ n’ by fs []
  \\ gvs [LESS_EQ_EXISTS,EXP_ADD]
QED

Theorem cv_rep_word_lsr[cv_rep]:
  from_word (word_lsr (w:'a word) n)
  =
  cv_div (from_word w) (cv_exp (Num 2) (Num n))
Proof
  gvs [cv_rep_def] \\ rw [] \\ gvs []
  \\ gvs [from_word_def,cv_exp_def,w2n_lsr]
QED

Theorem word_asr_add[cv_inline]:
  w ≫ n =
  let x = w in
  if word_msb (x :'a word) then
    (dimindex (:'a) − 1 '' dimindex (:α) − n) UINT_MAXw + (x ⋙ n)
  else x ⋙ n
Proof
  simp []
  \\ dep_rewrite.DEP_REWRITE_TAC [WORD_ADD_OR]
  \\ conj_tac >-
   (gvs [fcpTheory.CART_EQ,word_and_def,word_bits_def,
          wordsTheory.word_0,fcpTheory.FCP_BETA,word_slice_def]
    \\ rpt strip_tac \\ CCONTR_TAC \\ gvs [word_T,word_lsr_def]
    \\ gvs [fcpTheory.FCP_BETA])
  \\ rw [word_asr]
QED

(*----------------------------------------------------------*
   word comparisons (unsigned and signed)
 *----------------------------------------------------------*)

Theorem cv_word_lo_thm[cv_rep]:
  b2c (word_lo w1 w2) = cv_lt (from_word w1) (from_word w2)
Proof
  fs [from_word_def] \\ rw [WORD_LO]
QED

Theorem cv_word_hi_thm[cv_rep]:
  b2c (word_hi w2 w1) = cv_lt (from_word w1) (from_word w2)
Proof
  fs [from_word_def] \\ rw [WORD_HI]
QED

Theorem cv_word_hs_thm[cv_rep]:
  b2c (word_hs w1 w2) = cv_sub (Num 1) (cv_lt (from_word w1) (from_word w2))
Proof
  simp [GSYM cv_word_hi_thm,GSYM cv_rep_not,WORD_HS,WORD_HI,
        GREATER_EQ,GREATER_DEF,NOT_LESS]
QED

Theorem cv_word_ls_thm[cv_rep]:
  b2c (word_ls w1 w2) = cv_sub (Num 1) (cv_lt (from_word w2) (from_word w1))
Proof
  simp [GSYM cv_word_hi_thm,GSYM cv_rep_not]
  \\ rw [WORD_HI,WORD_LS,NOT_LESS,arithmeticTheory.GREATER_DEF]
QED

Definition cv_word_lt_def:
  cv_word_lt w1 w2 msb1 msb2 =
    cv_if (cv_eq msb1 msb2)
          (cv_lt w1 w2)
          (cv_if msb1 (Num 1) (cv_sub (Num 1) msb2))
End

Theorem cv_word_lt_thm[cv_rep]:
  b2c (word_lt w1 w2)
  =
  cv_word_lt (from_word w1) (from_word (w2:'a word))
             (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
             (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1))))
Proof
  rewrite_tac [GSYM cv_rep_word_msb] \\ simp [Once EQ_SYM_EQ]
  \\ gvs [cv_word_lt_def]
  \\ ‘∀b1 b2. (c2b (cv_eq (b2c b1) (b2c b2)) = (b1 = b2)) ∧ (c2b (b2c b1) = b1)’ by
    (Cases \\ Cases \\ gvs [])
  \\ simp [GSYM cv_word_lo_thm,GSYM cv_rep_not,wordsTheory.WORD_LT,WORD_LO]
  \\ rw [] \\ gvs []
QED

Theorem cv_word_gt_thm[cv_rep]:
  b2c (word_gt w2 w1)
  =
  cv_word_lt (from_word w1) (from_word (w2:'a word))
             (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
             (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1))))
Proof
  rewrite_tac [wordsTheory.WORD_GREATER,cv_word_lt_thm]
QED

Theorem cv_word_le_thm[cv_rep]:
  b2c (word_le w2 w1)
  =
  cv_sub (Num 1)
         (cv_word_lt (from_word w1) (from_word (w2:'a word))
                     (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
                     (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1)))))
Proof
  rewrite_tac [GSYM cv_word_lt_thm,GSYM cv_rep_not,WORD_NOT_LESS]
QED

Theorem cv_word_ge_thm[cv_rep]:
  b2c (word_ge w1 w2)
  =
  cv_sub (Num 1)
         (cv_word_lt (from_word w1) (from_word (w2:'a word))
                     (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
                     (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1)))))
Proof
  rewrite_tac [cv_word_le_thm,wordsTheory.WORD_GREATER_EQ]
QED

(*----------------------------------------------------------*
   word bits, slice, extract, concat
 *----------------------------------------------------------*)

Triviality MIN_lemma:
  l ≠ 0 ⇒ MIN k (l - 1) + 1 = MIN (k+1) l
Proof
  rw [MIN_DEF] \\ gvs []
QED

Theorem cv_word_bits_thm[cv_rep]:
  from_word (word_bits h l (w:'a word))
  =
  cv_div (cv_mod (from_word w)
                 (cv_exp (Num 2) (cv_min (cv_add (Num h) (Num 1)) (Num (dimindex (:'a))))))
         (cv_exp (Num 2) (Num l))
Proof
  simp [Once EQ_SYM_EQ]
  \\ ‘w = n2w (w2n w)’ by fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ rewrite_tac [word_bits_n2w,bitTheory.BITS_THM2,cv_add_def,GSYM cv_min_thm,
                  cv_exp_def,c2n_def]
  \\ gvs [from_word_def,ADD1,MIN_lemma,w2n_lt]
  \\ gvs [DIV_LT_X]
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ irule_at (Pos hd) arithmeticTheory.MOD_LESS_EQ
  \\ gvs []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ irule_at (Pos hd) w2n_lt
  \\ gvs []
QED

Theorem cv_word_slice_thm[cv_rep]:
  from_word (word_slice h l (w:'a word))
  =
  cv_mod (cv_mul
    (cv_div (cv_mod (from_word w)
                   (cv_exp (Num 2) (cv_min (cv_add (Num h) (Num 1)) (Num (dimindex (:'a))))))
            (cv_exp (Num 2) (Num l)))
     (Num (2 ** l))) (Num (dimword (:α)))
Proof
  rewrite_tac [GSYM cv_word_bits_thm,wordsTheory.WORD_SLICE_THM]
  \\ rewrite_tac [cv_rep_word_lsl,cv_exp_def] \\ fs []
  \\ simp [from_word_def,dimword_def]
QED

Theorem cv_word_extract[cv_rep] =
  “from_word (word_extract h l (w:'a word) : 'b word)”
  |> SIMP_CONV std_ss [word_extract_def,cv_rep_word_w2w,cv_word_bits_thm];

Triviality word_join_add:
  FINITE 𝕌(:'a) ∧ FINITE 𝕌(:'b) ⇒
  word_join (v:'a word) (w:'b word) =
  (w2w v ≪ dimindex (:β)) + w2w w
Proof
  simp [word_join_def]
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ rw []
  \\ irule WORD_ADD_OR
  \\ gvs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,word_lsl_def,w2w]
  \\ gvs [fcpTheory.index_sum,wordsTheory.word_0,NOT_LESS]
  \\ metis_tac []
QED


Theorem cv_word_join_thm[cv_rep]:
  FINITE 𝕌(:'a) ∧ FINITE 𝕌(:'b) ⇒
  from_word (word_join (w1:'a word) (w2:'b word))
  =
  cv_add (cv_mul (from_word w1) (cv_exp (Num 2) (Num (dimindex (:'b)))))
         (from_word w2)
Proof
  simp [word_join_add, cv_rep_word_add, cv_rep_word_lsl, cv_rep_word_w2w]
  \\ gvs [fcpTheory.index_sum]
  \\ gvs [from_word_def,cv_add_def,cv_mod_def,cv_mul_def,cv_exp_def]
  \\ gvs [GSYM dimword_def]
  \\ ‘(dimword (:β) * w2n w1) < 2 ** (dimindex (:α) + dimindex (:β))’ by
   (once_rewrite_tac [ADD_COMM]
    \\ rewrite_tac [EXP_ADD,dimword_def,LT_MULT_LCANCEL]
    \\ simp [GSYM dimword_def,w2n_lt])
  \\ rpt strip_tac \\ gvs []
  \\ qsuff_tac ‘(w2n w2 + dimword (:'b) * w2n w1) < dimword (:α + β)’ >- fs []
  \\ simp [dimword_def] \\ gvs [fcpTheory.index_sum,EXP_ADD]
  \\ irule LESS_LESS_EQ_TRANS
  \\ rewrite_tac [GSYM dimword_def]
  \\ qexists_tac ‘SUC (w2n w1) * dimword (:β)’
  \\ gvs [LE_MULT_RCANCEL] \\ gvs [DECIDE “SUC n ≤ k ⇔ n < k”, w2n_lt]
  \\ gvs [MULT_CLAUSES,w2n_lt]
QED

Theorem cv_word_concat_thm[cv_rep] =
  “from_word (((w1:'a word) @@ (w2:'b word)) :'c word)”
    |> REWRITE_CONV [word_concat_def,cv_rep_word_w2w,
                     UNDISCH cv_word_join_thm]
    |> DISCH_ALL
    |> SIMP_RULE std_ss [fcpTheory.index_sum];

(*----------------------------------------------------------*
   word or, and, xor
 *----------------------------------------------------------*)

Definition cv_word_or_loop_def:
  cv_word_or_loop x y =
    if c2b (cv_lt (Num 0) x) then
      cv_add (cv_mul (Num 2) (cv_word_or_loop (cv_div x (Num 2)) (cv_div y (Num 2))))
             (cv_max (cv_mod x (Num 2)) (cv_mod y (Num 2)))
    else y
Termination
  WF_REL_TAC ‘measure (c2n o FST)’ \\ Cases \\ fs [] \\ rw []
End

Theorem cv_word_or_loop_def[allow_rebind] = cv_word_or_loop_def
  |> REWRITE_RULE [GSYM cvTheory.cv_if]

Definition cv_word_or_def:
  cv_word_or x y =
    cv_if (cv_lt x y)
      (cv_word_or_loop x y)
      (cv_word_or_loop y x)
End

Definition cv_word_and_loop_def:
  cv_word_and_loop x y =
    if c2b (cv_lt (Num 0) x) then
      cv_add (cv_mul (Num 2) (cv_word_and_loop (cv_div x (Num 2)) (cv_div y (Num 2))))
             (cv_div (cv_add (cv_mod x (Num 2)) (cv_mod y (Num 2))) (Num 2))
    else (Num 0)
Termination
  WF_REL_TAC ‘measure (c2n o FST)’ \\ Cases \\ fs [] \\ rw []
End

Theorem cv_word_and_loop_def[allow_rebind] = cv_word_and_loop_def
  |> REWRITE_RULE [GSYM cvTheory.cv_if]

Definition cv_word_and_def:
  cv_word_and x y =
    cv_if (cv_lt x y)
      (cv_word_and_loop x y)
      (cv_word_and_loop y x)
End

Definition cv_word_xor_loop_def:
  cv_word_xor_loop x y =
    if c2b (cv_lt (Num 0) x) then
      cv_add (cv_mul (Num 2) (cv_word_xor_loop (cv_div x (Num 2)) (cv_div y (Num 2))))
             (cv_mod (cv_add (cv_mod x (Num 2)) (cv_mod y (Num 2))) (Num 2))
    else y
Termination
  WF_REL_TAC ‘measure (c2n o FST)’ \\ Cases \\ fs [] \\ rw []
End

Theorem cv_word_xor_loop_def[allow_rebind] = cv_word_xor_loop_def
  |> REWRITE_RULE [GSYM cvTheory.cv_if]

Definition cv_word_xor_def:
  cv_word_xor x y =
    cv_if (cv_lt x y)
      (cv_word_xor_loop x y)
      (cv_word_xor_loop y x)
End

Theorem BITWISE_ADD:
  ∀l k m n b.
    BITWISE (l + k) b m n =
    BITWISE l b m n +
    BITWISE k b (m DIV 2 ** l) (n DIV 2 ** l) * 2 ** l
Proof
  Induct_on ‘k’
  \\ fs [bitTheory.BITWISE_def,arithmeticTheory.ADD_CLAUSES]
  \\ rw [] \\ rewrite_tac [arithmeticTheory.ADD_ASSOC,arithmeticTheory.EQ_ADD_RCANCEL]
  \\ simp_tac std_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  \\ simp_tac std_ss [AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM]
  \\ simp_tac std_ss [arithmeticTheory.LEFT_ADD_DISTRIB]
  \\ simp_tac std_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  \\ simp_tac std_ss [AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM]
  \\ simp [DECIDE “m + n = n + k ⇔ m = k:num”]
  \\ simp_tac std_ss [Once arithmeticTheory.MULT_COMM]
  \\ rewrite_tac [GSYM bitTheory.SBIT_MULT]
  \\ rewrite_tac [GSYM bitTheory.BIT_SHIFT_THM4]
QED

Theorem BITWISE:
  BITWISE 0 b m n = 0 ∧
  BITWISE (SUC k) b m n =
  (if b (ODD m) (ODD n) then 1 else 0) + 2 * BITWISE k b (m DIV 2) (n DIV 2)
Proof
  rewrite_tac [DECIDE “SUC n = 1 + n”,BITWISE_ADD] \\ gvs []
  \\ rewrite_tac [DECIDE “1 = SUC 0”,bitTheory.BITWISE_def] \\ gvs []
  \\ gvs [bitTheory.SBIT_def,bitTheory.BIT0_ODD]
QED

Theorem cv_word_and_loop_thm:
  ∀m n.
    m ≤ n ∧ n < dimword (:'a) ⇒
    cv_word_and_loop (Num m) (Num n) = Num (w2n (n2w m && n2w n :'a word))
Proof
  simp [wordsTheory.word_and_n2w,wordsTheory.dimword_def,bitTheory.BITWISE_LT_2EXP]
  \\ Q.SPEC_TAC (‘dimindex (:'a)’,‘l’)
  \\ completeInduct_on ‘m’
  \\ simp [Once cv_word_and_loop_def]
  \\ Cases_on ‘m = 0’ \\ fs [wordsTheory.WORD_AND_CLAUSES]
  >-
   (qsuff_tac ‘∀l n. BITWISE l $/\ 0 n = 0’ >- fs []
    \\ Induct \\ fs [BITWISE])
  \\ gvs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ Cases_on ‘l’ \\ gvs []
  \\ rename [‘n < 2 ** SUC l’]
  \\ gvs [BITWISE]
  \\ first_x_assum $ qspecl_then [‘m DIV 2’,‘l’,‘n DIV 2’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ irule_at Any arithmeticTheory.DIV_LE_MONOTONE \\ gvs [])
  \\ strip_tac \\ gvs [bitTheory.BITWISE_LT_2EXP,wordsTheory.dimword_def]
  \\ Cases_on ‘ODD m’
  \\ Cases_on ‘ODD n’
  \\ imp_res_tac bitTheory.ODD_MOD2_LEM
  \\ gvs [arithmeticTheory.ODD_EVEN]
  \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs []
QED

Theorem cv_word_or_loop_thm:
  ∀m n.
    m ≤ n ∧ n < dimword (:'a) ⇒
    cv_word_or_loop (Num m) (Num n) = Num (w2n (n2w m || n2w n :'a word))
Proof
  simp [wordsTheory.word_or_n2w,wordsTheory.dimword_def,bitTheory.BITWISE_LT_2EXP]
  \\ Q.SPEC_TAC (‘dimindex (:'a)’,‘l’)
  \\ completeInduct_on ‘m’
  \\ simp [Once cv_word_or_loop_def]
  \\ Cases_on ‘m = 0’ \\ fs [wordsTheory.WORD_OR_CLAUSES]
  >-
   (Induct \\ fs [BITWISE]
    \\ rpt strip_tac
    \\ ‘0 < 2:num’ by fs []
    \\ drule_then strip_assume_tac arithmeticTheory.DIVISION
    \\ pop_assum $ qspec_then ‘n’ mp_tac \\ strip_tac
    \\ pop_assum kall_tac
    \\ pop_assum (fn th => simp [Once th])
    \\ first_x_assum $ qspec_then ‘n DIV 2’ mp_tac
    \\ impl_tac >- gvs []
    \\ disch_then (fn th => simp [Once th])
    \\ Cases_on ‘ODD n’
    \\ imp_res_tac bitTheory.ODD_MOD2_LEM \\ gvs []
    \\ gvs [arithmeticTheory.ODD_EVEN]
    \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs [])
  \\ gvs [PULL_FORALL,AND_IMP_INTRO,GSYM cv_max_thm] \\ rw []
  \\ Cases_on ‘l’ \\ gvs []
  \\ rename [‘n < 2 ** SUC l’]
  \\ gvs [BITWISE]
  \\ first_x_assum $ qspecl_then [‘m DIV 2’,‘l’,‘n DIV 2’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ irule_at Any arithmeticTheory.DIV_LE_MONOTONE \\ gvs [])
  \\ strip_tac \\ gvs [bitTheory.BITWISE_LT_2EXP,wordsTheory.dimword_def]
  \\ Cases_on ‘ODD m’
  \\ Cases_on ‘ODD n’
  \\ imp_res_tac bitTheory.ODD_MOD2_LEM
  \\ gvs []
  \\ gvs [arithmeticTheory.ODD_EVEN]
  \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs []
QED

Theorem cv_word_xor_loop_thm:
  ∀m n.
    m ≤ n ∧ n < dimword (:'a) ⇒
    cv_word_xor_loop (Num m) (Num n) = Num (w2n (word_xor (n2w m) (n2w n) :'a word))
Proof
  simp [wordsTheory.word_xor_n2w,wordsTheory.dimword_def,bitTheory.BITWISE_LT_2EXP]
  \\ Q.SPEC_TAC (‘dimindex (:'a)’,‘l’)
  \\ completeInduct_on ‘m’
  \\ simp [Once cv_word_xor_loop_def]
  \\ Cases_on ‘m = 0’ \\ fs [wordsTheory.WORD_XOR_CLAUSES]
  >-
   (Induct \\ fs [BITWISE]
    \\ rpt strip_tac
    \\ ‘0 < 2:num’ by fs []
    \\ drule_then strip_assume_tac arithmeticTheory.DIVISION
    \\ pop_assum $ qspec_then ‘n’ mp_tac \\ strip_tac
    \\ pop_assum kall_tac
    \\ pop_assum (fn th => simp [Once th])
    \\ first_x_assum $ qspec_then ‘n DIV 2’ mp_tac
    \\ impl_tac >- gvs []
    \\ disch_then (fn th => simp [Once th])
    \\ Cases_on ‘ODD n’
    \\ imp_res_tac bitTheory.ODD_MOD2_LEM \\ gvs []
    \\ gvs [arithmeticTheory.ODD_EVEN]
    \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs [])
  \\ gvs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ Cases_on ‘l’ \\ gvs []
  \\ rename [‘n < 2 ** SUC l’]
  \\ gvs [BITWISE]
  \\ first_x_assum $ qspecl_then [‘m DIV 2’,‘l’,‘n DIV 2’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ irule_at Any arithmeticTheory.DIV_LE_MONOTONE \\ gvs [])
  \\ strip_tac \\ gvs [bitTheory.BITWISE_LT_2EXP,wordsTheory.dimword_def]
  \\ ‘0 < 2:num’ by fs []
  \\ drule arithmeticTheory.MOD_PLUS
  \\ disch_then (fn th => simp_tac std_ss [Once (GSYM th)])
  \\ Cases_on ‘ODD m’
  \\ Cases_on ‘ODD n’
  \\ imp_res_tac bitTheory.ODD_MOD2_LEM
  \\ full_simp_tac std_ss [arithmeticTheory.ODD_EVEN]
  \\ imp_res_tac arithmeticTheory.EVEN_MOD2
  \\ full_simp_tac std_ss [arithmeticTheory.ODD_EVEN]
QED

Theorem cv_rep_word_and[cv_rep]:
  from_word (w1 && w2)
  =
  cv_word_and (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ rw [cv_word_and_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ Cases_on ‘n < n'’ \\ gvs []
  >-
   (‘n ≤ n'’ by fs [] \\ pop_assum mp_tac \\ pop_assum kall_tac \\ rw []
    \\ drule_all cv_word_and_loop_thm
    \\ strip_tac \\ gvs [])
  \\ gvs [arithmeticTheory.NOT_LESS]
  \\ drule_all cv_word_and_loop_thm
  \\ strip_tac \\ gvs []
  \\ simp [Once wordsTheory.WORD_AND_COMM]
QED

Theorem cv_rep_word_or[cv_rep]:
  from_word (w1 || w2)
  =
  cv_word_or (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ rw [cv_word_or_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ Cases_on ‘n < n'’ \\ gvs []
  >-
   (‘n ≤ n'’ by fs [] \\ pop_assum mp_tac \\ pop_assum kall_tac \\ rw []
    \\ drule_all cv_word_or_loop_thm
    \\ strip_tac \\ gvs [])
  \\ gvs [arithmeticTheory.NOT_LESS]
  \\ drule_all cv_word_or_loop_thm
  \\ strip_tac \\ gvs []
  \\ simp [Once wordsTheory.WORD_OR_COMM]
QED

Theorem cv_rep_word_xor[cv_rep]:
  from_word (word_xor w1 w2)
  =
  cv_word_xor (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ rw [cv_word_xor_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ Cases_on ‘n < n'’ \\ gvs []
  >-
   (‘n ≤ n'’ by fs [] \\ pop_assum mp_tac \\ pop_assum kall_tac \\ rw []
    \\ drule_all cv_word_xor_loop_thm
    \\ strip_tac \\ gvs [])
  \\ gvs [arithmeticTheory.NOT_LESS]
  \\ drule_all cv_word_xor_loop_thm
  \\ strip_tac \\ gvs []
  \\ simp [Once wordsTheory.WORD_XOR_COMM]
QED

Theorem cv_rep_word_not[cv_rep]:
  from_word (¬ w :'a word)
  =
  cv_word_xor (from_word w) (Num (2 ** dimindex (:'a) - 1))
Proof
  ‘¬w = w ⊕ UINT_MAXw’ by fs [WORD_XOR_CLAUSES]
  \\ asm_rewrite_tac [cv_rep_word_xor, cv_rep_word_uint_max]
QED

val _ = export_theory();
