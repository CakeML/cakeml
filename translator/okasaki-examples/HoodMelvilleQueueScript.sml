
open HolKernel Parse boolLib bossLib; val _ = new_theory "HoodMelvilleQueue";

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory;

val _ = translation_extends "mini_prelude";

(* implementation *)

val _ = Hol_datatype `
  status =
     Idle
   | Reversing of num => 'a list => 'a list => 'a list => 'a list
   | Appending of num => 'a list => 'a list
   | Finished of 'a list`;

val _ = Hol_datatype `
  queue = QUEUE of num => 'a list => 'a status => num => 'a list`;

val exec_def = mlDefine `
  exec s = case s of
    Reversing ok (x::f) f' (y::r) r' => Reversing (ok+1) f (x::f') r (y::r')
  | Reversing ok [] f' [y] r' => Appending ok f' (y::r')
  | Appending 0 f' r' => Finished r'
  | Appending ok (x::f') r' => Appending (ok-1) f' (x::r')
  | s => s`

val invalidate_def = mlDefine `
  invalidate s = case s of
    Reversing ok f f' r r' => Reversing (ok-1) f f' r r'
  | Appending 0 f' (x::r') => Finished r'
  | Appending ok f' r' => Appending (ok-1) f' r'
  | s => s`;

val exec2_def = mlDefine `
  exec2 (QUEUE lenf f state lenr r) =
    case exec (exec state) of
      Finished newf => QUEUE lenf newf Idle lenr r
    | newstate => QUEUE lenf f newstate lenr r`;

val check_def = mlDefine `
  check (QUEUE lenf f state lenr r) =
    if lenr <= lenf
       then exec2 (QUEUE lenf f state lenr r)
       else let newstate = Reversing 0 f [] r [] in
            exec2 (QUEUE (lenf+lenr) f newstate 0 [])`

val empty_def = mlDefine `
  empty = QUEUE 0 [] Idle 0 []`

val is_empty_def = mlDefine `
  is_empty lenf _ _ _ _ = (lenf = 0)`;

val snoc_def = mlDefine `
  snoc (QUEUE lenf f state lenr r) x =
    check (QUEUE lenf f state (lenr+1) (x::r))`;

val head_def = mlDefine `
  head (QUEUE _ (x::_) _ _ _) = x`;

val tail_def = mlDefine `
  tail (QUEUE lenf (x::f) state lenr r) =
    check (QUEUE (lenf-1) f (invalidate state) lenr r)`;

(* verification proof

val base_def = Define `
  base lf lenf lenr r g q =
    (lenr = LENGTH r) /\ (lenf = lf) /\ (q = g ++ REVERSE r)`;

val oper_def = Define `
  oper lenf f lenr r g q d n m p =
    base (2 * m + 1 - p) lenf lenr r g q /\
    (n + d = 2 * p + 2 * lenr + 2) /\
    (m = LENGTH f + p) /\
    isPREFIX f q`;

val reve_def = Define `
  reve f f' f'' r' r'' g ok n m p =
    (g = REVERSE (TAKE ok f') ++ f'' ++ REVERSE r'' ++ r') /\
    (n = LENGTH f') /\
    (m = LENGTH f'' + n) /\
    (n = LENGTH r') /\
    (m + 1 = LENGTH r'' + n)`;

val appe_def = Define `
  appe f f' r' g ok n m p =
    (g = REVERSE (TAKE ok f') ++ r') /\
    (LENGTH f' + n = 2 * m + 1) /\
    (LENGTH r' = n) /\
    (ok + n + p = 2 * m + 1) /\
    m <= n /\ n <= 2 * m + 1`

val prop_def = Define `
  prop c d (QUEUE lenf f s lenr r) q =
    case s of
      Idle => base (LENGTH f) lenf lenr r f q /\ lenr <= lenf
    | Finished f' => c /\ base (LENGTH f') lenf lenr r f' q /\ lenr <= lenf
    | Reversing ok f'' f' r'' r' => ?n m p g.
        oper lenf f lenr r g q d n m p /\ reve f f' f'' r' r'' g ok n m p
    | Appending ok f' r' => ?n m p g.
        oper lenf f lenr r g q d n m p /\ appe f f' r' g ok n m p`;

val queue_inv_def = Define `
  queue_inv q q' = prop F 0 q' q`;

*)

val _ = export_theory();
