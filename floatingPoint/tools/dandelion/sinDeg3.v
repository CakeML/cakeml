Require Import Interval.Tactic.
Require Import Reals.

Goal
forall (x:R),((858993459/8589934592 <= x <= 1) ->
Rabs (sin (x) - (-1499276771 / 2199023255552 +
(x * (541190871 / 536870912) +
 (x * x * (-3581686363 / 137438953472) +
  x * x * x * (-1202115613 / 8589934592)))))
	<=
	946027/4294967296)%R.
Proof.
intros.
time interval with (i_bisect x, i_taylor x).
Qed.