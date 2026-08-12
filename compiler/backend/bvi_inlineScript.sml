(*
  A deliberately small BVI inliner for CPR worker-wrapper functions.

  This pass is name preserving.  It only substitutes wrappers satisfying
  [wrapper_ok]; extending that predicate is the intended way to support a
  new worker-wrapper protocol.
*)
Theory bvi_inline
Ancestors
  bvi backend_common
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

Definition bvi_mk_tick_def:
  bvi_mk_tick n e = FUNPOW bvi$Tick n e
End

(* First-order form for cv_compute, which has no [FUNPOW]. *)
Theorem bvi_mk_tick_eq:
  bvi_mk_tick n e = if n = 0 then e else bvi$Tick (bvi_mk_tick (n − 1) e)
Proof
  Cases_on ‘n’ >> simp [bvi_mk_tick_def, FUNPOW_SUC]
QED

(* [Op] reverses its argument list, so a wrapper that boxes the worker's
   [rets] results in order lists them reversed under the [Cons]. *)
Definition canonical_wrapper_def:
  (canonical_wrapper name arity
     (bvi$LetCall rets ticks worker args
        (bvi$Op (BlockOp (Cons tag)) rvs)) ⇔
     worker ≠ name ∧
     args = GENLIST bvi$Var arity ∧
     rvs = REVERSE (GENLIST bvi$Var rets)) ∧
  (canonical_wrapper name arity _ ⇔ F)
End

Definition wrapper_ok_def:
  wrapper_ok name arity body ⇔ canonical_wrapper name arity body
End

(* [cs] is a cache of code-table entries.  The correctness invariant
   needed for a hit is that the cached label, arity, and body correspond
   to the code table (up to the expression relation used by the pass). *)
Definition inline_exp_def:
  (inline_exp cs (bvi$Var n) = bvi$Var n) ∧
  (inline_exp cs (bvi$If x y z) =
     bvi$If (inline_exp cs x) (inline_exp cs y) (inline_exp cs z)) ∧
  (inline_exp cs (bvi$Let xs y) =
     bvi$Let (inline_exps cs xs) (inline_exp cs y)) ∧
  (inline_exp cs (bvi$Raise x) = bvi$Raise (inline_exp cs x)) ∧
  (inline_exp cs (bvi$Tick x) = bvi$Tick (inline_exp cs x)) ∧
  (inline_exp cs (bvi$Call ticks dest xs handler) =
     let xs = inline_exps cs xs in
       case handler of
       | SOME h => bvi$Call ticks dest xs (SOME (inline_exp cs h))
       | NONE =>
           case dest of
           | NONE => bvi$Call ticks NONE xs NONE
           | SOME name =>
               case lookup name cs of
               | NONE => bvi$Call ticks (SOME name) xs NONE
               | SOME (arity,body) =>
                   if LENGTH xs = arity then
                     bvi$Let xs (bvi_mk_tick (SUC ticks) body)
                   else bvi$Call ticks (SOME name) xs NONE) ∧
  (inline_exp cs (bvi$Force loc n) = bvi$Force loc n) ∧
  (inline_exp cs (bvi$Op op xs) = bvi$Op op (inline_exps cs xs)) ∧
  (inline_exp cs (bvi$LetCall rets ticks dest xs y) =
     bvi$LetCall rets ticks dest (inline_exps cs xs) (inline_exp cs y)) ∧
  (inline_exp cs (bvi$Return xs) = bvi$Return (inline_exps cs xs)) ∧
  (inline_exps cs [] = []) ∧
  (inline_exps cs (x::xs) = inline_exp cs x :: inline_exps cs xs)
Termination
  WF_REL_TAC ‘measure $ λx. pmatch x of
    | INL (_,e) => bvi$exp_size e
    | INR (_,es) => bvi$exp2_size es’
  >> rpt strip_tac >> simp [bviTheory.exp_size_def]
End

Definition inline_all_def:
  (inline_all cs [] = (cs,[])) ∧
  (inline_all cs ((name,arity,body)::prog) =
     let body = inline_exp cs body in
     let cs1 = if wrapper_ok name arity body then
                 insert name (arity,body) cs
               else cs in
     let (cs2,prog2) = inline_all cs1 prog in
       (cs2,(name,arity,body)::prog2))
End

Definition remove_ticks_exp_def:
  (remove_ticks_exp (bvi$Var n) = bvi$Var n) ∧
  (remove_ticks_exp (bvi$If x y z) =
     bvi$If (remove_ticks_exp x) (remove_ticks_exp y)
       (remove_ticks_exp z)) ∧
  (remove_ticks_exp (bvi$Let xs y) =
     bvi$Let (remove_ticks_exps xs) (remove_ticks_exp y)) ∧
  (remove_ticks_exp (bvi$Raise x) = bvi$Raise (remove_ticks_exp x)) ∧
  (remove_ticks_exp (bvi$Tick x) = remove_ticks_exp x) ∧
  (remove_ticks_exp (bvi$Call ticks dest xs handler) =
     bvi$Call 0 dest (remove_ticks_exps xs)
       (OPTION_MAP remove_ticks_exp handler)) ∧
  (remove_ticks_exp (bvi$Force loc n) = bvi$Force loc n) ∧
  (remove_ticks_exp (bvi$Op op xs) = bvi$Op op (remove_ticks_exps xs)) ∧
  (remove_ticks_exp (bvi$LetCall rets ticks dest xs y) =
     bvi$LetCall rets 0 dest (remove_ticks_exps xs)
       (remove_ticks_exp y)) ∧
  (remove_ticks_exp (bvi$Return xs) =
     bvi$Return (remove_ticks_exps xs)) ∧
  (remove_ticks_exps [] = []) ∧
  (remove_ticks_exps (x::xs) =
     remove_ticks_exp x :: remove_ticks_exps xs)
Termination
  WF_REL_TAC ‘measure $ λx. pmatch x of
    | INL e => bvi$exp_size e
    | INR es => bvi$exp2_size es’
  >> rpt strip_tac >> simp [bviTheory.exp_size_def]
End

Definition compile_inc_def:
  compile_inc cs prog =
    let (cs1,prog1) = inline_all cs prog in
      (cs1,MAP (λ(name,arity,body).
                  (name,arity,remove_ticks_exp body)) prog1)
End

Definition compile_prog_def:
  compile_prog prog = compile_inc LN prog
End

Theorem canonical_four_result_wrapper:
  wrapper_ok 10 3
    (LetCall 4 0 11 (GENLIST Var 3)
      (Op (BlockOp (Cons 7)) (REVERSE (GENLIST Var 4))))
Proof
  EVAL_TAC
QED

Theorem malformed_wrappers_rejected:
  ¬wrapper_ok 10 3
      (LetCall 4 0 10 (GENLIST Var 3)
        (Op (BlockOp (Cons 7)) (GENLIST Var 4))) ∧
  ¬wrapper_ok 10 3
      (LetCall 4 0 11 [Var 0; Var 2; Var 1]
        (Op (BlockOp (Cons 7)) (GENLIST Var 4))) ∧
  ¬wrapper_ok 10 3
      (LetCall 4 0 11 (GENLIST Var 3)
        (Op (BlockOp (Cons 7)) [Var 0; Var 1; Var 2])) ∧
  ¬wrapper_ok 10 3 (Return (GENLIST Var 3))
Proof
  EVAL_TAC
QED

Theorem inline_boundary_examples:
  inline_exp (insert 10 (3,
      LetCall 4 0 11 (GENLIST Var 3)
        (Op (BlockOp (Cons 7)) (GENLIST Var 4))) LN)
    (Call 2 (SOME 10) [Var 4; Var 5; Var 6] NONE) =
      Let [Var 4; Var 5; Var 6]
        (bvi_mk_tick 3
          (LetCall 4 0 11 (GENLIST Var 3)
            (Op (BlockOp (Cons 7)) (GENLIST Var 4)))) ∧
  inline_exp (insert 10 (3,
      LetCall 4 0 11 (GENLIST Var 3)
        (Op (BlockOp (Cons 7)) (GENLIST Var 4))) LN)
    (Call 2 (SOME 10) [Var 4; Var 5; Var 6] (SOME (Var 0))) =
      Call 2 (SOME 10) [Var 4; Var 5; Var 6] (SOME (Var 0)) ∧
  inline_exp (insert 10 (3,
      LetCall 4 0 11 (GENLIST Var 3)
        (Op (BlockOp (Cons 7)) (GENLIST Var 4))) LN)
    (LetCall 1 2 10 [Var 4; Var 5; Var 6] (Return [Var 0])) =
      LetCall 1 2 10 [Var 4; Var 5; Var 6] (Return [Var 0])
Proof
  EVAL_TAC
QED

Theorem final_tick_cleanup_example:
  remove_ticks_exp
    (Tick (Call 2 (SOME 10) [Tick (Var 0)]
      (SOME (LetCall 1 3 11 [Tick (Var 1)] (Return [Var 0]))))) =
    Call 0 (SOME 10) [Var 0]
      (SOME (LetCall 1 0 11 [Var 1] (Return [Var 0])))
Proof
  EVAL_TAC
QED
