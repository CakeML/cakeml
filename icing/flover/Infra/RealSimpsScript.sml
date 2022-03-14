open RealArith;
open realTheory realLib;
open preambleFloVer;
  (*
val _ = ParseExtras.temp_tight_equality() *)

val _ = new_theory "RealSimps";

val _ = temp_overload_on("abs",``real$abs``);
val _ = temp_overload_on("max",``real$max``);

val abs_leq_zero = store_thm (
  "abs_leq_zero[simp]",
  ``!v. abs v <= 0 <=> v = 0``,
  rw[realTheory.abs] \\ RealArith.REAL_ASM_ARITH_TAC);

val REAL_INV_LE_ANTIMONO = store_thm ("REAL_INV_LE_ANTIMONO",
  ``! x y. 0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)``,
  rpt strip_tac
  \\ `inv x < inv y <=> y < x`
    by (MATCH_MP_TAC REAL_INV_LT_ANTIMONO \\ fs [])
  \\ EQ_TAC
  \\ fs [REAL_LE_LT]
  \\ STRIP_TAC
  \\ fs [REAL_INV_INJ]);

val REAL_INV_LE_ANTIMONO_IMPR = store_thm ("REAL_INV_LE_ANTIMONO_IMPR",
  ``! x y. 0 < x /\ 0 < y /\ y <= x ==> inv x <= inv y``,
  rpt strip_tac \\ fs[REAL_INV_LE_ANTIMONO]);

val REAL_INV_LE_ANTIMONO_IMPL = store_thm ("REAL_INV_LE_ANTIMONO_IMPL",
  ``! x y. x <0 /\ y < 0 /\ y <= x ==> inv x <= inv y``,
  rpt strip_tac
  \\ once_rewrite_tac [GSYM REAL_LE_NEG]
  \\ `- inv y = inv (- y)` by (irule REAL_NEG_INV \\ REAL_ASM_ARITH_TAC)
  \\ `- inv x = inv (- x)` by (irule REAL_NEG_INV \\ REAL_ASM_ARITH_TAC)
  \\ ntac 2(FIRST_X_ASSUM (fn thm => once_rewrite_tac [ thm]))
  \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[]);

val REAL_MUL_LE_COMPAT_NEG_L = store_thm( "REAL_MUL_LE_COMPAT_NEG_L",
``!(a:real) b c. a <= &0 /\ b <= c ==> a * c <= a * b``,
  rpt strip_tac
  \\ once_rewrite_tac [SYM (SPEC ``a:real`` REAL_NEG_NEG)]
  \\ once_rewrite_tac [SYM (SPECL [``a:real``, ``c:real``] REAL_MUL_LNEG)]
  \\ once_rewrite_tac [REAL_LE_NEG]
  \\ `0 <= - (a:real)`
    by (once_rewrite_tac [SYM (SPEC ``-(a:real)`` REAL_NEG_LE0)]
        \\ fs [REAL_NEG_NEG])
  \\ match_mp_tac REAL_LE_LMUL_IMP \\ fs[]);

val maxAbs = store_thm ("maxAbs",
  ``!p q (r:real). (p <= q) /\ (q <= r) ==> (abs q <= max (abs p) (abs r))``,
  rpt strip_tac
  \\ simp [REAL_LE_MAX]
  \\ REAL_ASM_ARITH_TAC);

val maxAbs_def = Define `
  maxAbs iv = max (abs (FST iv)) (abs (SND iv))`;

val Rabs_err_simpl = store_thm("Rabs_err_simpl",
  ``!(a:real) (b:real). abs (a - (a * (1 + b))) = abs (a * b)``,
  rpt strip_tac \\ REAL_ASM_ARITH_TAC);

val machineEpsilon_def = Define `machineEpsilon = 1/ (2 pow 53)`;

val real_le_trans2 = store_thm ("real_le_trans2",
``!(y:real) x z. x <= y /\ y <= z ==> x <= z``, metis_tac[REAL_LE_TRANS]);

val mEps_geq_zero = store_thm ("mEps_geq_zero",
``0 <= machineEpsilon``, once_rewrite_tac[machineEpsilon_def] \\ EVAL_TAC);

val err_up = store_thm ("err_up",
  ``!a b (c:real).
     0 <= c /\
     a - b <= c /\
     0 < a - b ==>
     b <= a + c``,
  REAL_ASM_ARITH_TAC);

val REAL_LE_ADD_FLIP = store_thm ("REAL_LE_ADD_FLIP",
  ``!a b (c:real).
     a - b <= c ==>
     a - c <= b``,
  REAL_ASM_ARITH_TAC);

val triangle_trans = store_thm (
  "triangle_trans",
  ``!a b c.
      abs (a + b) <= abs a + abs b /\
      abs a + abs b <= c ==>
      abs (a + b) <= c``,
  rpt strip_tac
  \\ REAL_ASM_ARITH_TAC);

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
