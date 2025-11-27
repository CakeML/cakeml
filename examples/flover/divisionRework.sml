Theorem divisionErrorBounded:
  !(e1lo e1hi nR1 e2lo e2hi nR2 nF1 nF2 err1 err2:real).
    (e1lo <= nR1) /\ (nR1 <= e1hi) /\
    (e2lo <= nR2) /\ (nR2 <= e2hi) /\
    abs (nR1 − nF1) <= err1 /\
    abs (nR2 − nF2) <= err2 /\
    0 <= err1 /\
    0 <= err2 /\
    contained nF1 (widenInterval (e1lo,e1hi) err1) /\
    contained nF2 (widenInterval (e2lo,e2hi) err2) /\
    noDivzero e2hi e2lo /\
    noDivzero (SND (widenInterval (e2lo,e2hi) err2))
    (FST (widenInterval (e2lo,e2hi) err2)) ==>
    abs (nR1 / nR2 − nF1 / nF2) ≤
    maxAbs (e1lo,e1hi) *
         (1 /
          (minAbsFun (widenInterval (e2lo,e2hi) err2) *
           minAbsFun (widenInterval (e2lo,e2hi) err2)) * err2) +
         maxAbs (invertInterval (e2lo,e2hi)) * err1 +
         err1 *
         (1 /
          (minAbsFun (widenInterval (e2lo,e2hi) err2) *
           minAbsFun (widenInterval (e2lo,e2hi) err2)) * err2)
Proof
  rpt strip_tac
  \\ `contained (inv nR2) (invertInterval (e2lo, e2hi))`
       by (irule interval_inversion_valid \\ conj_tac
           \\ fs[contained_def, IVlo_def, IVhi_def, noDivzero_def])
  \\ `contained (inv nF2) (invertInterval (widenInterval (e2lo, e2hi) err2))`
       by (irule interval_inversion_valid \\ conj_tac
           \\ fs[contained_def, IVlo_def, IVhi_def, noDivzero_def])
  \\ `nR1 <= maxAbs (e1lo, e1hi)`
       by (irule contained_leq_maxAbs_val
            \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `inv nR2 <= maxAbs (invertInterval(e2lo, e2hi))`
       by (irule contained_leq_maxAbs_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `-nR1 <= maxAbs (e1lo, e1hi)`
       by (irule contained_leq_maxAbs_neg_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `- inv nR2 <= maxAbs (invertInterval (e2lo, e2hi))`
       by (irule contained_leq_maxAbs_neg_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `nR1 * err2 <= maxAbs (e1lo, e1hi) * err2`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `-nR1 * err2 <= maxAbs (e1lo, e1hi) * err2`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `inv nR2 * err1 <= maxAbs (invertInterval(e2lo, e2hi)) * err1`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `- inv nR2 * err1 <= maxAbs (invertInterval(e2lo, e2hi)) * err1`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `- (err1 * err2) <= err1 * err2`
        by (rewrite_tac[REAL_NEG_LMUL] \\ irule REAL_LE_RMUL_IMP
            \\ REAL_ASM_ARITH_TAC)
  \\ `0 <= maxAbs (e1lo, e1hi) * err2` by REAL_ASM_ARITH_TAC
  \\ `0 <= maxAbs (invertInterval (e2lo, e2hi)) * err1` by REAL_ASM_ARITH_TAC
  \\ `maxAbs (e1lo, e1hi) * err2 <=
      maxAbs (e1lo, e1hi) * err2 + maxAbs (invertInterval (e2lo, e2hi)) * err1`
       by (REAL_ASM_ARITH_TAC)
  \\ `maxAbs (e1lo, e1hi) * err2 + maxAbs (invertInterval(e2lo, e2hi)) * err1 <=
      maxAbs (e1lo, e1hi) * err2 + maxAbs (invertInterval (e2lo, e2hi)) * err1 + err1 * err2`
       by REAL_ASM_ARITH_TAC
  \\ ntac 2 (first_x_assum (fn thm1 => (mp_then Any assume_tac REAL_LE_ABS_TRANS thm1 \\ mp_tac thm1)))
  \\ rpt strip_tac
   (* Case distinction for divisor range
      positive or negative in float and real valued execution *)
  \\ fs [IVlo_def, IVhi_def, widenInterval_def, contained_def, noDivzero_def]
  (* Solve trivial, bogus cases *)
  \\ TRY (`e2hi < e2lo` by REAL_ASM_ARITH_TAC \\ REAL_ASM_ARITH_TAC)
  (* e2hi + err2 < 0, e2hi < 0;
     The range of the divisor lies in the range from -infinity until 0 *)
  >- (
   `abs (inv nR2 - inv nF2) <= err2 * inv ((e2hi + err2) * (e2hi + err2))`
     by (irule err_prop_inversion_neg \\ fs[] \\ qexists_tac `e2lo` \\ simp[])
   \\ fs [widenInterval_def, IVlo_def, IVhi_def]
   \\ `minAbsFun (e2lo - err2, e2hi + err2) = - (e2hi + err2)`
       by (irule minAbs_negative_iv_is_hi \\ REAL_ASM_ARITH_TAC)
   \\ simp[]
   \\ qpat_x_assum `minAbsFun _ = _ ` kall_tac
   \\ `nF1 <= nR1 + err1` by REAL_ASM_ARITH_TAC
   \\ `nR1 - err1 <= nF1` by REAL_ASM_ARITH_TAC
   \\ `(0 < nR2 - nF2 /\ nR2 - nF2 <= err2) \/ (nR2 - nF2 <= 0 /\ - (nR2 - nF2) <= err2)`
       by REAL_ASM_ARITH_TAC
   (* 0 < nR2 - nF2; nR2 - nF2 ≤ err2 *)
   >- (
    `nF2 < nR2` by REAL_ASM_ARITH_TAC
    \\ qpat_x_assum `nF2 < nR2` (fn thm => assume_tac (ONCE_REWRITE_RULE [GSYM REAL_LT_NEG] thm))
    \\ `inv (- nF2) < inv (- nR2)` by (irule REAL_LT_INV \\ REAL_ASM_ARITH_TAC)
    \\ `inv (- nF2) = - (inv nF2)` by (irule (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC)
    \\ `inv (- nR2) = - (inv nR2)` by (irule (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC)
    \\ rpt (qpat_x_assum `inv (- _) = - (inv _)`
            (fn thm => rule_assum_tac (fn hyp => REWRITE_RULE [thm] hyp)))
    \\ `inv nR2 < inv nF2` by REAL_ASM_ARITH_TAC
    \\ qpat_x_assum `- _ < - _` kall_tac
    \\ `inv nR2 - inv nF2 < 0` by REAL_ASM_ARITH_TAC
    \\ `- (nR2⁻¹ − nF2⁻¹) ≤ err2 * ((e2hi + err2) * (e2hi + err2))⁻¹`
      by (fs[] \\ REAL_ASM_ARITH_TAC)
    \\ `inv nF2 <= inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2))`
      by REAL_ASM_ARITH_TAC
    \\ `inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)) <= inv nF2`
      by REAL_ASM_ARITH_TAC
    (* Next do a case distinction for the absolute value *)
    \\ `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC
    \\ qpat_x_assum `!x. A /\ B \/ C`
                      (qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)`
                       DISJ_CASES_TAC)
    \\ fs[realTheory.abs]
    (* 0 ≤ nR1 / nR2 - nF1 / nF2 *)
    >- (
      fs[real_sub, real_div]
      \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
      (* nF1 < 0 *)
      >- (
        irule REAL_LE_TRANS
        \\ qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2hi + err2) pow 2))`
        \\ conj_tac
        >- (
          fs[REAL_LE_LADD] \\ rewrite_tac [REAL_NEG_LMUL]
          \\ irule REAL_LE_LMUL_IMP \\ conj_tac \\ REAL_ASM_ARITH_TAC)
        \\ qabbrev_tac `err_inv = err2 * inv ((e2hi + err2) pow 2)`
        \\ qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* inv nR2 + err_inv < 0 *)
        >- (irule REAL_LE_TRANS
            \\ qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)`
            \\ conj_tac
            >- (fs [REAL_LE_ADD])
            \\ real_rewrite `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                    - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
            \\ rewrite_tac [real_sub, GSYM REAL_ADD_ASSOC]
            \\ irule REAL_LE_ADD2 \\ conj_tac
            >- (unabbrev_all_tac
                \\ fs[REAL_POW_INV]
                \\ once_rewrite_tac [REAL_NEG_LMUL]
                \\ once_rewrite_tac [REAL_NEG_RMUL]
                \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
                \\ irule REAL_LE_LMUL_IMP
                \\ conj_tac \\ fs[]
                \\ irule REAL_LE_RMUL_IMP \\ fs[])
            \\ irule REAL_LE_ADD2 \\ conj_tac
            >- (once_rewrite_tac [REAL_NEG_RMUL]
                \\ real_rewrite `- (inv nR2) * err1 = err1 * - (inv nR2)`
                \\ irule REAL_LE_LMUL_IMP
                \\ conj_tac \\ fs[])
            \\ unabbrev_all_tac
            \\ fs[REAL_POW_INV]
            \\ irule REAL_LE_TRANS \\ qexists_tac `0`
            \\ conj_tac \\ fs[REAL_NEG_LE0, REAL_LE_MUL])
        (* 0 ≤ inv nR2 + err_inv *)
        \\ irule REAL_LE_TRANS
        \\ qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)`
        \\ conj_tac
        >- (fs [REAL_LE_ADD]
            \\ irule REAL_LE_RMUL_IMP
            \\ conj_tac \\ REAL_ASM_ARITH_TAC)
        \\ real_rewrite `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                        - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
        \\ unabbrev_all_tac
        \\ rewrite_tac [real_sub, GSYM REAL_ADD_ASSOC]
        \\ irule REAL_LE_ADD2 \\ conj_tac
        >- (rewrite_tac [GSYM REAL_MUL_ASSOC]
            \\ real_rewrite `-nR1 * (err2 * (inv ((e2hi + err2) pow 2))) =
                             err2 * (-nR1 * (inv ((e2hi + err2) pow 2)))`
            \\ irule REAL_LE_LMUL_IMP
            \\ conj_tac \\ fs[REAL_POW_INV]
            \\ irule REAL_LE_RMUL_IMP \\ fs[])
        \\ irule REAL_LE_ADD2 \\ conj_tac
        >- (real_rewrite `inv nR2 * err1 = err1 * inv nR2`
            \\ irule REAL_LE_LMUL_IMP
            \\ conj_tac \\ fs[])
        \\ fs[REAL_POW_INV])
      (* 0 ≤ nF1 *)
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2hi + err2) pow 2))`
      \\ conj_tac
      >- (fs[REAL_LE_LADD]
          \\ once_rewrite_tac [REAL_NEG_LMUL]
          \\ irule REAL_MUL_LE_COMPAT_NEG_L
          \\ conj_tac \\ REAL_ASM_ARITH_TAC)
      \\ qabbrev_tac `err_inv = (err2 * inv ((e2hi + err2) pow 2))`
      \\ qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
      (* inv nR2 - err_inv < 0 *)
      >- (irule REAL_LE_TRANS
          \\ qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)`
          \\ conj_tac
          >- (fs [REAL_LE_ADD]
              \\ once_rewrite_tac [REAL_MUL_COMM]
              \\ irule REAL_MUL_LE_COMPAT_NEG_L
              \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
              \\ fs [REAL_LE_NEG])
          \\ real_rewrite `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                          nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
          \\ qunabbrev_tac `err_inv`
          \\ irule REAL_LE_ADD2
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ irule REAL_LE_ADD2
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
          \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
          \\ irule REAL_LE_RMUL_IMP
          \\ fs[REAL_LE_POW2, REAL_LE_MUL])
      (* 0 ≤ inv nR2 - err_inv *)
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `nR1 * inv nR2 + - (nR1 - err1) * (inv nR2 - err_inv)`
      \\ conj_tac
      >- (fs [REAL_LE_ADD]
          \\ irule REAL_LE_RMUL_IMP
          \\ conj_tac \\ REAL_ASM_ARITH_TAC)
      \\ real_rewrite `nR1 * inv nR2 + - (nR1 - err1) * (inv nR2 - err_inv) =
                      nR1 * err_inv + inv nR2 * err1 + - err1 * err_inv`
      \\ qunabbrev_tac `err_inv`
      \\ irule REAL_LE_ADD2 \\ conj_tac
      >- (
        irule REAL_LE_ADD2 \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
        \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
        \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
        \\ irule REAL_LE_RMUL_IMP
        \\ fs[REAL_LE_POW2, REAL_LE_MUL])
      \\ irule REAL_LE_TRANS \\ qexists_tac `0`
      \\ fs[REAL_LE_POW2, REAL_LE_MUL])
    (* nR1 / nR2 - nF1 / nF2 < 0; Absolute value negative *)
    \\ fs[real_sub, real_div]
    \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
    (* nF1 < 0 *)
    >- (
      irule REAL_LE_TRANS
      \\ qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2hi + err2) pow 2))`
      \\ conj_tac
      >- (once_rewrite_tac [REAL_NEG_ADD, GSYM REAL_NEG_LMUL]
          \\ fs[REAL_LE_LADD, real_sub])
      \\ qabbrev_tac `err_inv = err2 * inv ((e2hi + err2) pow 2)`
      \\ qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
      (*  inv nR2 - err_inv < 0 *)
      >- (irule REAL_LE_TRANS
          \\ qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)`
          \\ conj_tac
          >- (fs [REAL_LE_ADD, real_sub])
          \\ real_rewrite `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
          \\ qunabbrev_tac `err_inv`
          \\ irule REAL_LE_ADD2
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ irule REAL_LE_ADD2
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
          \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
          \\ irule REAL_LE_RMUL_IMP
          \\ fs[REAL_LE_POW2, REAL_LE_MUL])
      (*  0 ≤ inv nR2 - err_inv *)
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)`
      \\ conj_tac
      >- (fs [REAL_LE_ADD]
          \\ irule REAL_LE_RMUL_IMP
          \\ conj_tac \\ REAL_ASM_ARITH_TAC)
      \\ real_rewrite `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
            - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
      \\ qunabbrev_tac `err_inv` \\ rewrite_tac [real_sub]
      \\ irule REAL_LE_ADD2 \\ conj_tac
      >- (irule REAL_LE_ADD2
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_POW_INV]
          \\ once_rewrite_tac [REAL_NEG_LMUL]
          \\ once_rewrite_tac [REAL_NEG_RMUL]
          \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
          \\ irule REAL_LE_LMUL_IMP
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ irule REAL_LE_RMUL_IMP
          \\ fs[REAL_LE_POW2, REAL_LE_MUL])
      \\ irule REAL_LE_TRANS \\ qexists_tac `0`
      \\ fs[REAL_LE_POW2, REAL_LE_MUL])
    (* 0 <= nF1 *)
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2hi + err2) pow 2))`
    \\ conj_tac
    >- (fs[REAL_LE_LADD, REAL_NEG_ADD]
        \\ irule REAL_LE_LMUL_IMP \\ REAL_ASM_ARITH_TAC)
    \\ qabbrev_tac `err_inv = (err2 * inv ((e2hi + err2) pow 2))`
    \\ qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
    (* inv nR2 + err_inv < 0 *)
    >- (irule REAL_LE_TRANS
        \\ qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)`
        \\ conj_tac
        >- (fs [REAL_LE_ADD, real_sub])
        \\ real_rewrite `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
        \\ qunabbrev_tac `err_inv`
        \\ simp[real_sub]
        \\ irule REAL_LE_ADD2 \\ conj_tac
        >- (irule REAL_LE_ADD2
            \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
            \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
            \\ irule REAL_LE_LMUL_IMP \\ fs[REAL_POW_INV]
            \\ irule REAL_LE_RMUL_IMP
            \\ fs[REAL_LE_POW2, REAL_LE_MUL])
        \\ irule REAL_LE_TRANS \\ qexists_tac `0`
        \\ fs[REAL_LE_POW2, REAL_LE_MUL])
    (* 0 ≤ inv nR2 + err_inv *)
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)`
    \\ conj_tac
    >- (fs [REAL_LE_ADD]
        \\ irule REAL_LE_RMUL_IMP
        \\ conj_tac \\ REAL_ASM_ARITH_TAC)
    \\ real_rewrite `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                    nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
    \\ qunabbrev_tac `err_inv`
    \\ irule REAL_LE_ADD2
    \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
    \\ irule REAL_LE_ADD2
    \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
    \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
    \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
    \\ irule REAL_LE_RMUL_IMP
    \\ fs[REAL_LE_POW2, REAL_LE_MUL])
   (* - (nR2 - nF2) ≤ err2; nR2 - nF2 < 0;
      Absolute value negative *)
   \\ fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2]
   \\ `nR2 <= nF2` by REAL_ASM_ARITH_TAC
   \\ qpat_x_assum `nR2 <= nF2` (fn thm => assume_tac (ONCE_REWRITE_RULE [GSYM REAL_LE_NEG] thm))
   \\ `inv (- nR2) <= inv (- nF2)` by (irule REAL_INV_LE_ANTIMONO_IMPR \\ REAL_ASM_ARITH_TAC)
   \\ `inv (- nR2) = - (inv nR2)` by (irule (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC)
   \\ `inv (- nF2) = - (inv nF2)` by (irule (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC)
   \\ rpt (
      qpat_x_assum `inv (- _) = - (inv _)`
      (fn thm => rule_assum_tac (fn hyp => REWRITE_RULE [thm] hyp)))
   \\ `inv nF2 <= inv nR2` by REAL_ASM_ARITH_TAC
   \\ qpat_x_assum `- _ <= - _` kall_tac
   \\ `0 <= inv nR2 - inv nF2` by REAL_ASM_ARITH_TAC
   \\ `(inv nR2 − inv nF2) ≤ err2 * inv ((e2hi + err2) pow 2)` by REAL_ASM_ARITH_TAC
   \\ `inv nF2 <= inv nR2 + err2 * inv ((e2hi + err2) pow 2)` by REAL_ASM_ARITH_TAC
   \\ `inv nR2 - err2 * inv ((e2hi + err2) pow 2) <= inv nF2` by REAL_ASM_ARITH_TAC
   (* Next do a case distinction for the absolute value *)
   \\ `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC
   \\ qpat_x_assum `!x. A /\ B \/ C`
                     (qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)` DISJ_CASES_TAC)
   \\ fs[real_sub, real_div, REAL_NEG_ADD, realTheory.abs]
   (* Combine with a case split for nF1 *)
   \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* 0 ≤ nR1 * inv nR2 + - (nF1 * inv nF2); nF1 < 0*)
   >- (
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2)))`
    \\ conj_tac
    >- (fs[REAL_LE_LADD] \\ once_rewrite_tac [REAL_NEG_LMUL]
        \\ irule REAL_LE_LMUL_IMP
        \\ conj_tac \\ REAL_ASM_ARITH_TAC)
    \\ qabbrev_tac `err_inv = (err2 * inv ((e2hi + err2) pow 2))`
    \\ qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
    (* inv nR2 + err_inv < 0 *)
    >- (
      irule REAL_LE_TRANS
      \\ qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)`
      \\ conj_tac
      >- (fs [REAL_LE_ADD])
      \\ real_rewrite `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                      - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
      \\ qunabbrev_tac `err_inv`
      \\ rewrite_tac[real_sub]
      \\ irule REAL_LE_ADD2
      \\ conj_tac
      >- (irule REAL_LE_ADD2
          \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
          \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
          \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
          \\ irule REAL_LE_RMUL_IMP
          \\ fs[REAL_LE_POW2, REAL_LE_MUL])
      \\ irule REAL_LE_TRANS \\ qexists_tac `0`
      \\ fs[REAL_LE_POW2, REAL_LE_MUL])
    (* 0 ≤ inv nR2 + err_inv *)
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)`
    \\ conj_tac
    >- (fs [REAL_LE_ADD]
        \\ irule REAL_LE_RMUL_IMP
        \\ conj_tac \\ REAL_ASM_ARITH_TAC)
    \\ real_rewrite `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                        - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
    \\ qunabbrev_tac `err_inv`
    \\ irule REAL_LE_ADD2
    \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
    \\ irule REAL_LE_ADD2
    \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
    \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
    \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
    \\ irule REAL_LE_RMUL_IMP
    \\ fs[REAL_LE_POW2, REAL_LE_MUL])
   (* 0 ≤ nR1 * inv nR2 + - (nF1 * inv nF2); 0 ≤ nF1 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2hi + err2) pow 2))`
     \\ conj_tac
     >- (fs[REAL_LE_LADD] \\ once_rewrite_tac [REAL_NEG_LMUL]
         \\ irule REAL_MUL_LE_COMPAT_NEG_L
         \\ conj_tac \\ REAL_ASM_ARITH_TAC)
     \\ qabbrev_tac `err_inv = (err2 * inv ((e2hi + err2) pow 2))` \\
     \\ qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* inv nR2 - err_inv < 0 *)
     >- (irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)`
         \\ conj_tac
         >- (fs [REAL_LE_ADD])
         \\ real_rewrite `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                        nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
         \\ qunabbrev_tac `err_inv`
         \\ irule REAL_LE_ADD2
         \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
         \\ irule REAL_LE_ADD2
         \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
         \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
         \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
         \\ irule REAL_LE_RMUL_IMP
         \\ fs[REAL_LE_POW2, REAL_LE_MUL])
     (* 0 <= inv nR2 - err_inv *)
     \\ irule REAL_LE_TRANS
     \\ qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)`
     \\ conj_tac
     >- (fs [REAL_LE_ADD]
         \\ irule REAL_LE_RMUL_IMP
         \\ conj_tac \\ REAL_ASM_ARITH_TAC)
     \\ real_rewrite `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
                     nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
     \\ qunabbrev_tac `err_inv` \\ rewrite_tac[real_sub]
     \\ irule REAL_LE_ADD2 \\ conj_tac
     >- (irule REAL_LE_ADD2
         \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
         \\ real_rewrite `err2 * maxAbs (e1lo, e1hi) = maxAbs (e1lo, e1hi) * err2`
         \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
         \\ irule REAL_LE_RMUL_IMP
         \\ fs[REAL_LE_POW2, REAL_LE_MUL])
     \\ rewrite_tac [REAL_NEG_LMUL]
     \\ irule REAL_LE_TRANS \\ qexists_tac `0`
     \\ fs[REAL_LE_POW2, REAL_LE_MUL])
   (* nR1 * inv nR2 + - (nF1 * inv nF2) < 0; nF1 < 0 *)
   >- (
      )
   \\
   )
  (* 0 < e2lo, 0 < e2lo - err2;
     The range of the divisor is positive *)
  \\

  (* Case 2: Absolute value negative; nF1 < 0 *)
              >- (irule REAL_LE_TRANS \\
                qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  irule REAL_MUL_LE_COMPAT_NEG_L \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (irule REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                       once_rewrite_tac [REAL_MUL_COMM] \\
                      irule REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                       - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      irule REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      irule REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      irule REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC))
                  >- (irule REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      irule REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                       - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp [real_sub] \\
                      irule REAL_LE_ADD2 \\
                      conj_tac
                      >- (irule REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        irule REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                        irule REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))))
              (* 0 <= - nF1 *)
              >- (irule REAL_LE_TRANS \\
                qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  irule REAL_LE_LMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (irule REAL_LE_TRANS \\
                    qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      once_rewrite_tac [REAL_MUL_COMM] \\
                      irule REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp[real_sub] \\
                      irule REAL_LE_ADD2 \\
                      conj_tac
                      >- (irule REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        irule REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (fs [REAL_NEG_LMUL] \\
                        irule REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))
                  >- (irule REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      irule REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      irule REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      irule REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      irule REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)))))

(* The range of the divisor lies in the range from 0 to infinity *)
  >- (rule_assum_tac
      (fn thm =>
                REWRITE_RULE[IVlo_def, IVhi_def, widenInterval_def, contained_def, invertInterval_def] thm) \\
     `abs (inv nR2 - inv nF2) <= err2 * (inv ((e2lo - err2) * (e2lo -err2)))`
               by (irule err_prop_inversion_pos \\
                   qexists_tac `e2hi` \\ rpt(conj_tac) \\
                   fs[contained_def, IVlo_def, IVhi_def]) \\
     fs [widenInterval_def, IVlo_def, IVhi_def, invertInterval_def] \\
     `minAbsFun (e2lo - err2, e2hi + err2) = (e2lo - err2)`
               by (irule minAbs_positive_iv_is_lo \\ REAL_ASM_ARITH_TAC) \\
     simp[] \\
     qpat_x_assum `minAbsFun _ = _ ` kall_tac \\
     `nF1 <= err1 + nR1` by REAL_ASM_ARITH_TAC \\
     `nR1 - err1 <= nF1` by REAL_ASM_ARITH_TAC \\
     `(nR2 - nF2 > 0 /\ nR2 - nF2 <= err2) \/ (nR2 - nF2 <= 0 /\ - (nR2 - nF2) <= err2)`
               by REAL_ASM_ARITH_TAC
    (* Positive case for abs (nR2 - nF2) <= err2 *)
    >- (`nF2 < nR2` by REAL_ASM_ARITH_TAC \\
      `inv nR2 < inv nF2` by (irule REAL_LT_INV \\ TRY REAL_ASM_ARITH_TAC) \\
      `inv nR2 - inv nF2 < 0` by REAL_ASM_ARITH_TAC \\
      `nR2⁻¹ − nF2⁻¹ ≤ err2 * ((e2lo - err2) * (e2lo - err2))⁻¹` by REAL_ASM_ARITH_TAC \\
      `inv nF2 <= inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2))` by REAL_ASM_ARITH_TAC \\
      `inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)) <= inv nF2` by REAL_ASM_ARITH_TAC \\
      (* Next do a case distinction for the absolute value *)
      `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC \\
      qpat_x_assum `!x. A /\ B \/ C`
        (fn thm => qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)` DISJ_CASES_TAC thm)
      \\ fs[realTheory.abs]
      (* Case 1: Absolute value positive *)
      >- (fs[real_sub, real_div, REAL_NEG_LMUL] \\
        qspecl_then [`-nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* -nF1 < 0 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + - err2) * (e2lo + - err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp[GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)))))
      (* Case 2: Absolute value negative *)
      >- (fs[real_sub, real_div, REAL_NEG_LMUL, REAL_NEG_ADD] \\
        qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* nF1 < 0 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                 once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))))))
    (* Negative case for abs (nR2 - nF2) <= err2 *)
    >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
      `nR2 <= nF2` by REAL_ASM_ARITH_TAC \\
      `inv nF2 <= inv nR2` by (irule REAL_INV_LE_ANTIMONO_IMPR \\ REAL_ASM_ARITH_TAC) \\
      `0 <= inv nR2 - inv nF2` by REAL_ASM_ARITH_TAC \\
      `(nR2⁻¹ − nF2⁻¹) ≤ err2 * ((e2lo - err2) * (e2lo - err2))⁻¹` by REAL_ASM_ARITH_TAC \\
      `inv nF2 <= inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2))` by REAL_ASM_ARITH_TAC \\
      `inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)) <= inv nF2` by REAL_ASM_ARITH_TAC \\
      (* Next do a case distinction for the absolute value *)
      `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC \\
      qpat_x_assum `!x. A /\ B \/ C`
        (fn thm => qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)` DISJ_CASES_TAC thm) \\
      fs[real_sub, real_div, REAL_NEG_LMUL, REAL_NEG_ADD, realTheory.abs]
      (* Case 1: Absolute value positive *)
      >- (qspecl_then [`-nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* -nF1 < 0 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)))))
      (* Case 2: Absolute value negative *)
      >- (qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* nF1 < 0 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                 once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (irule REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            irule REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (irule REAL_LE_TRANS \\
              qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                irule REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                irule REAL_LE_ADD2 \\
                conj_tac
                >- (irule REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [REAL_NEG_LMUL] \\
                  irule REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (irule REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                irule REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                irule REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)))))))
QED
