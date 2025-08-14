(**
  Real-number simplification theorems
**)
open RealArith;
open realTheory realLib;
open preambleFloVer;

val _ = new_theory "RealSimps";

Overload abs[local] = “realax$abs”
Overload max[local] = “realax$max”

Theorem abs_leq_zero[simp]:
  !v. abs v <= 0 <=> v = 0
Proof
  rw[realTheory.abs] \\ RealArith.REAL_ASM_ARITH_TAC
QED

Theorem REAL_INV_LE_ANTIMONO:
  ! x y. 0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)
Proof
  rpt strip_tac
  \\ `inv x < inv y <=> y < x`
    by (MATCH_MP_TAC REAL_INV_LT_ANTIMONO \\ fs [])
  \\ EQ_TAC
  \\ fs [REAL_LE_LT]
  \\ STRIP_TAC
  \\ fs [REAL_INV_INJ]
QED

Theorem REAL_INV_LE_ANTIMONO_IMPR:
  ! x y. 0 < x /\ 0 < y /\ y <= x ==> inv x <= inv y
Proof
  rpt strip_tac \\ fs[REAL_INV_LE_ANTIMONO]
QED

Theorem REAL_INV_LE_ANTIMONO_IMPL:
  ! x y. x <0 /\ y < 0 /\ y <= x ==> inv x <= inv y
Proof
  rpt strip_tac
  \\ once_rewrite_tac [GSYM REAL_LE_NEG]
  \\ `- inv y = inv (- y)` by (irule REAL_NEG_INV \\ REAL_ASM_ARITH_TAC)
  \\ `- inv x = inv (- x)` by (irule REAL_NEG_INV \\ REAL_ASM_ARITH_TAC)
  \\ ntac 2(FIRST_X_ASSUM (fn thm => once_rewrite_tac [ thm]))
  \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[]
QED

Theorem REAL_MUL_LE_COMPAT_NEG_L:
  !(a:real) b c. a <= &0 /\ b <= c ==> a * c <= a * b
Proof
  rpt strip_tac
  \\ once_rewrite_tac [SYM (SPEC ``a:real`` REAL_NEG_NEG)]
  \\ once_rewrite_tac [SYM (SPECL [``a:real``, ``c:real``] REAL_MUL_LNEG)]
  \\ once_rewrite_tac [REAL_LE_NEG]
  \\ `0 <= - (a:real)`
    by (once_rewrite_tac [SYM (SPEC ``-(a:real)`` REAL_NEG_LE0)]
        \\ fs [REAL_NEG_NEG])
  \\ match_mp_tac REAL_LE_LMUL_IMP \\ fs[]
QED

Theorem maxAbs:
  !p q (r:real). (p <= q) /\ (q <= r) ==> (abs q <= max (abs p) (abs r))
Proof
  rpt strip_tac
  \\ simp [REAL_LE_MAX]
  \\ REAL_ASM_ARITH_TAC
QED

Definition maxAbs_def:
  maxAbs iv = max (abs (FST iv)) (abs (SND iv))
End

Theorem Rabs_err_simpl:
  !(a:real) (b:real). abs (a - (a * (1 + b))) = abs (a * b)
Proof
  rpt strip_tac \\ REAL_ASM_ARITH_TAC
QED

Definition machineEpsilon_def:
  machineEpsilon = 1/ (2 pow 53)
End

Theorem real_le_trans2:
  !(y:real) x z. x <= y /\ y <= z ==> x <= z
Proof
  metis_tac[REAL_LE_TRANS]
QED

Theorem mEps_geq_zero:
  0 <= machineEpsilon
Proof
  once_rewrite_tac[machineEpsilon_def] \\ EVAL_TAC
QED

Theorem err_up:
  !a b (c:real).
     0 <= c /\
     a - b <= c /\
     0 < a - b ==>
     b <= a + c
Proof
  REAL_ASM_ARITH_TAC
QED

Theorem REAL_LE_ADD_FLIP:
  !a b (c:real).
    a - b <= c ==>
    a - c <= b
Proof
  REAL_ASM_ARITH_TAC
QED

Theorem triangle_trans:
  !a b c.
      abs (a + b) <= abs a + abs b /\
      abs a + abs b <= c ==>
      abs (a + b) <= c
Proof
  rpt strip_tac
  \\ REAL_ASM_ARITH_TAC
QED

Theorem REAL_LE_ABS_TRANS:
  ! a b.
    abs a <= b ==>
    a <= b
Proof
  rpt strip_tac \\ irule REAL_LE_TRANS
  \\ fsrw_tac [SATISFY_ss] [ABS_LE]
QED

Theorem REAL_POW_1OVER_POS[simp]:
  ∀ n. 0 <= 1 / 2 pow n
Proof
  rpt strip_tac
  \\ qspec_then `n` (fn thm => once_rewrite_tac [GSYM thm]) POW_ONE
  \\ rewrite_tac [GSYM REAL_POW_DIV]
  \\ irule POW_POS \\ fs[]
QED

val _ = export_theory();
