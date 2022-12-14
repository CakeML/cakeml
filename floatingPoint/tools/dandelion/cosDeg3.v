Require Import Interval.Tactic.
Require Import Reals.

Goal
forall (x:R),((858993459/8589934592 <= x <= 1) ->
Rabs (cos (x) - (4289449735 / 4294967296 +
(x * (139975391 / 8589934592) +
 (x * x * (-2408138823 / 4294967296) +
  x * x * x * (2948059219 / 34359738368)))))
	<=
	582015/2147483648)%R.
Proof.
intros.
time interval with (i_bisect x, i_taylor x).
Qed.