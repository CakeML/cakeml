(**
  f machine-precision as a datatype for mixed-precision computations

  @author: Raphael Monat
  @maintainer: Heiko Becker
 **)
open realTheory realLib;
open RealSimpsTheory;
open preambleFloVer;

val _ = new_theory "MachineType";

Overload abs[local] = “realax$abs”

val _ = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option"];

Datatype:
  mType = REAL | M16 | M32 | M64 | F num num bool (* first num is word length, second is fractional bits, bool is for sign of fractional bits *)
End

Definition isFixedPoint_def :
  isFixedPoint (F w f s) = T /\
  isFixedPoint _ = F
End

Definition maxExponent_def:
  (maxExponent (REAL) = 0n) /\
  (maxExponent (M16) = 15) /\
  (maxExponent (M32) = 127) /\
  (maxExponent (M64) = 1023) /\
  (maxExponent (F w f s) = f)
End

Definition minExponentPos_def:
  (minExponentPos (REAL) = 0n) /\
  (minExponentPos (M16) = 14) /\
  (minExponentPos (M32) = 126) /\
  (minExponentPos (M64) = 1022) /\
  (minExponentPos (F w f s) = f)
End

(**
Goldberg - Handbook of Floating-Point Arithmetic: (p.183)
(𝛃 - 𝛃^(1 - p)) * 𝛃^(e_max)
which simplifies to 2^(e_max) for base 2
**)
Definition maxValue_def:
  maxValue (m:mType) =
    case m of
    | F w f s => &((2n ** (w-1)) - 1) * (if s then &(2n ** (maxExponent m)) else inv (&(2n ** (maxExponent m))))
    | _ => (&(2n ** (maxExponent m))):real
End

(** Using the sign bit, the very same number is representable as a negative number,
  thus just apply negation here **)
Definition minValue_pos_def:
  minValue_pos (m:mType) =
    case m of
    | F w f s => 0
    | _ =>  inv (&(2n ** (minExponentPos m)))
End

(** Goldberg - Handbook of Floating-Point Arithmetic: (p.183)
  𝛃^(e_min -p + 1) = 𝛃^(e_min -1) for base 2
**)
Definition normal_def:
  normal (v:real) (m:mType) =
  (minValue_pos m <= abs v /\ abs v <= maxValue m)
End

Definition denormal_def:
  denormal (v:real) (m:mType) =
    case m of
      | REAL => F
      | _ => ((abs v) < (minValue_pos m) /\ v <> 0)
End

(** Return an upperbound on the error for value v committed by rounding
  For real numbers this is 0,
  For floating-point numbers, we have to first check whether the the value is
    denormal or normal. For denormal numbers, we use the upper bound
    1/2 * 2^(-e_min - p + 1) = 2^(-1) * 2^(-e_min - p + 1)) =
    2 ^(-1 - e_min - p + 1) = 2^(-(e_min + p)) = inv (2 ^(e_min + p))
    where p is the number of precision bits for the floating-point type
    For normal numbers the roundoff error is at most
      1/2 * 2^(1 - p) = 2^(-1) * 2^(1-p) = 2^(-1 + 1 -p) = 2^(-p) = inv (2^p)
    where p is the number of precision bits.
  For fixed-point numbers with f fractional bits, the truncation error is at
    maximum inv (2 pow f)
  see p. 24 of Handbook of Floating-Point Arithmetic for details *)
Definition mTypeToR_def:
  mTypeToR (m:mType) (v:real):real =
    case m of
      | REAL => 0
      | M16 => if (denormal v M16)
               then inv (2 pow (minExponentPos M16 + 11))
               else inv (2 pow 11)
      | M32 => if (denormal v M32)
               then inv(2 pow (minExponentPos M32 + 24))
               else inv (2 pow 24)
      | M64 => if (denormal v M64)
               then inv (2 pow (minExponentPos M64 + 53))
               else inv (2 pow 53)
      | F w f s => if s then (2 pow f) else inv (2 pow f)
End

Theorem mTypeToR_simp =
  SIMP_RULE std_ss
    (List.map EVAL [“minExponentPos M16”, “minExponentPos M32”, “minExponentPos M64”])
    mTypeToR_def

(** Compute the maximum error contributed by rounding a value v to type m,
    does not account for propagation errors, these must be accounted elsewhere *)
Definition computeError_def:
  computeError v m =
    case m of
    | REAL => 0
    | F w f s => mTypeToR m v
    | _ => if (denormal v m) then mTypeToR m v else abs v * mTypeToR m v
End

Theorem mTypeToR_pos:
  ∀ m v. 0 ≤ mTypeToR m v
Proof
  Cases_on `m` \\ fs[mTypeToR_def]
  \\ rpt strip_tac \\ COND_CASES_TAC \\ fs[]
QED

Theorem computeError_pos:
  0 ≤ computeError v m
Proof
  fs[computeError_def]
  \\ Cases_on ‘m’ \\ fs[mTypeToR_def]
  \\ COND_CASES_TAC \\ fs[]
QED

Theorem normal_not_denormal:
  normal x m ⇒ ~ denormal x m
Proof
  fs[normal_def, denormal_def] \\ Cases_on ‘m’ \\ fs[REAL_NOT_LT]
QED

(** Show that the roundoff error contributed by normal numbers is worse than the
    roundoff error contributed of any possible denormal number.
    This is the key theorem for integrating denormals with the 1+delta model *)
Theorem computeError_up:
  ∀ v a b m.
    abs v <= maxAbs (a,b) ⇒
    (* normal (maxAbs(a,b)) m ⇒ *)
    computeError v m <= computeError (maxAbs (a,b)) m
Proof
  rpt strip_tac \\ Cases_on ‘m’
  \\ fs[Excl "RMUL_LEQNORM", mTypeToR_def, computeError_def, maxAbs_def]
  \\ imp_res_tac normal_not_denormal
  \\ fs[Excl "RMUL_LEQNORM"]
  \\ ntac 2 COND_CASES_TAC
  \\ TRY (irule REAL_LE_LMUL_IMP \\ fs[] \\ irule REAL_LE_TRANS
          \\ qexists_tac ‘max (abs a) (abs b)’ \\ fs[ABS_LE])
  \\ fs[Excl "RMUL_LEQNORM", normal_def]
  \\ TRY (fs[Excl "RMUL_LEQNORM", denormal_def, REAL_NOT_LT]
          \\ ‘abs (max (abs a) (abs b)) = max (abs a) (abs b)’
            by (fs[REAL_LE_MAX])
          \\ ‘max (abs a) (abs b) < max (abs a) (abs b)’ suffices_by (fs[])
          \\ RealArith.REAL_ASM_ARITH_TAC)
  \\ fs[Excl "RMUL_LEQNORM", denormal_def]
  \\ TRY (‘abs v ≤ 0’ suffices_by (fs[])
          \\ pop_assum (rewrite_tac o single o GSYM)
          \\ fs[] \\ NO_TAC)
  \\ irule REAL_LE_TRANS
  THENL (map qexists_tac
         [‘1 / 2048 * minValue_pos M16’,
          ‘1 / 16777216 * minValue_pos M32’,
          ‘1 / 9007199254740992 * minValue_pos M64’])
  \\ conj_tac \\ TRY (irule REAL_LE_LMUL_IMP \\ fs[REAL_NOT_LT])
  \\ fs[minExponentPos_def, minValue_pos_def]
QED

(**
  Check if machine precision m1 is more precise than machine precision m2.
  REAL is real-valued evaluation, hence the most precise.
  All floating-point types are compared by
    mTypeToQ m1 <= mTypeToQ m2
  All fixed-point types are compared by comparing only the word size
  We consider a 32 bit fixed-point number to be more precise than a 16 bit
  fixed-point number, no matter what the fractional bits may be.
  For the moment, fixed-point and floating-point formats are incomparable.
 **)
Definition isMorePrecise_def:
  isMorePrecise (m1:mType) (m2:mType) =
    case m1, m2 of
    | REAL, _ => T
    | F w1 f1 s1, F w2 f2 s2 =>
                    if s1 then
                      if s2 then
                        (w2 ≤ w1 ∧ f2 ≤ f1)
                      else
                        (w2 ≤ w1)
                    else if s2 then F
                    else (w2 ≤ w1 ∧ f2 ≤ f1)
    | F w f s, _ => F
    | _, F w f s=> F
    | M16, M16 => T
    | M32, M32 => T
    | M32, M16 => T
    | M64, REAL => F
    | M64, _ => T
    | _, _ => F
End

(**
   More efficient version for performance, unfortunately we cannot do better
   for fixed-points
**)
Definition morePrecise_def:
  (morePrecise REAL _ = T) /\
  (morePrecise (F w1 f1 s1) (F w2 f2 s2) =
               (if s1 then
                  if s2 then
                    (w2 ≤ w1 ∧ f2 ≤ f1)
                  else
                    (w2 ≤ w1)
                else if s2 then F
                else (w2 ≤ w1 ∧ f2 ≤ f1))) ∧
  (morePrecise (F w f s) _ = F) /\
  (morePrecise _ (F w f s) = F) /\
  (morePrecise M16 M16 = T) /\
  (morePrecise M32 M32 = T) /\
  (morePrecise M32 M16 = T) /\
  (morePrecise M64 REAL = F) /\
  (morePrecise M64 _ = T) /\
  (morePrecise _ _ = F)
End

Theorem morePrecise_trans:
  !m1 m2 m3.
    morePrecise m1 m2 /\
    morePrecise m2 m3 ==>
    morePrecise m1 m3
Proof
  rpt strip_tac
  \\ Cases_on `m1` \\ Cases_on `m2` \\ Cases_on `m3`
  \\ fs[morePrecise_def]
  \\ every_case_tac \\ gs[]
QED

Theorem isMorePrecise_morePrecise:
  !m1 m2.
    isMorePrecise m1 m2 = morePrecise m1 m2
Proof
  rpt strip_tac
  \\ Cases_on `m1` \\ Cases_on `m2`
  \\ once_rewrite_tac [morePrecise_def, isMorePrecise_def]
  \\ fs[morePrecise_def, isMorePrecise_def, mTypeToR_def]
QED

Theorem isMorePrecise_refl:
  !m. isMorePrecise m m
Proof
  Cases_on `m` \\ EVAL_TAC \\ fs[]
QED

Theorem REAL_least_precision:
  !(m:mType).
      isMorePrecise m REAL ==> m = REAL
Proof
  fs [isMorePrecise_def, mTypeToR_def]
  \\ rpt strip_tac
  \\ Cases_on `m`
  \\ fs []
QED

Theorem REAL_lower_bound:
  !(m:mType).
      isMorePrecise REAL m
Proof
  Cases_on `m` \\ EVAL_TAC
QED

(**
  Function computing the join of two precisions, this is the most precise type,
  in which evaluation has to be performed, e.g. addition of 32 and 64 bit floats
  has to happen in 64 bits
**)
Definition join_fl_def:
  join_fl (F w1 f1 s1) (F w2 f2 s2) = NONE /\
  join_fl m1 m2 = if (morePrecise m1 m2) then SOME m1 else SOME m2
End

Definition join_fl3_def:
  join_fl3 m1 m2 m3 = do mj <- join_fl m1 m2; join_fl mj m3; od
End

(** Since we cannot compute a join for Fixed-Points, we give a
    isJoin predicate which returns true for fixed-points, but needs to inspect
    it for floating-points **)
Definition isCompat_def:
  isCompat (REAL) (REAL) = T /\
  isCompat (F w1 f1 s1) (F w2 f2 s2) = morePrecise (F w2 f2 s2) (F w1 f1 s1) /\
  isCompat (F _ _ _) _ = F /\
  isCompat _ (F _ _ _) = F /\
  isCompat m1 m2 = (m1 = m2)
End

Definition isJoin_def:
  isJoin m1 m2 mj =
    if (isFixedPoint m1 /\ isFixedPoint m2)
    then morePrecise m1 mj /\ morePrecise m2 mj
    else
      (case join_fl m1 m2 of
      |NONE => F
      |SOME mNew => mNew = mj)
End

Definition isJoin3_def:
  isJoin3 m1 m2 m3 mj =
    if (isFixedPoint m1 /\ isFixedPoint m2 /\ isFixedPoint m3)
    then morePrecise m1 mj /\ morePrecise m2 mj /\ morePrecise m3 mj
    else
      (case join_fl3 m1 m2 m3 of
       |NONE => F
       |SOME mNew => mNew = mj)
End

(**
  Predicate that is true if and only if the given value v is a valid
  floating-point value according to the the type m.
  Since we use the 1 + 𝝳 abstraction, the value must either be
  in normal range or 0.
**)
Definition validFloatValue_def:
  validFloatValue (v:real) (m:mType) =
   case m of
    | REAL => T
    | _ => normal v m \/ denormal v m \/ v = 0
End

Definition validValue_def:
  validValue (v:real) (m:mType) =
    case m of
      | REAL => T
      | _ => abs v <= maxValue m
End

Theorem no_underflow_fixed_point:
  !v f w. ~ denormal v (F w f s)
Proof
  fs[denormal_def, minValue_pos_def, REAL_NOT_LT, REAL_ABS_POS]
QED

val _ = export_theory();
