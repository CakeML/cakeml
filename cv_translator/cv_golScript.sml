(*
  Sketch of symbolic conway's game-of-life evaluation
*)
open HolKernel Parse boolLib bossLib;
open cv_transLib cv_stdTheory

val _ = new_theory "cv_gol";

Datatype:
  var = A num | B num
End

Datatype:
  bool_exp =
  | False
  | True
  | Var var
  | Not bool_exp
  | Or bool_exp bool_exp
  | And bool_exp bool_exp
  | If var bool_exp bool_exp
End

Definition to_bool_def:
  to_bool e True = T ∧
  to_bool e False = F ∧
  to_bool e (Var v) = e v ∧
  to_bool e (Not x) = ~ (to_bool e x) ∧
  to_bool e (Or x y) = (to_bool e x ∨ to_bool e y) ∧
  to_bool e (And x y) = (to_bool e x ∧ to_bool e y) ∧
  to_bool e (If v x y) = if e v then to_bool e x else to_bool e y
End

Definition SmartIf_def:
  SmartIf v x y =
    if x = True ∧ y = False then Var v else
    if x = False ∧ y = True then Not (Var v) else
    if x = y then x else
    if x = True then Or (Var v) y else
    if y = False then And (Var v) x else
    if x = False then And (Not (Var v)) y else
    if y = True then Or (Not (Var v)) x else If v x y
End

Theorem to_bool_SmartIf[simp]:
  to_bool e (SmartIf v x y) = to_bool e (If v x y)
Proof
  rw [SmartIf_def,to_bool_def]
QED

Definition all_vars_def:
  all_vars True acc = acc ∧
  all_vars False acc = acc ∧
  all_vars (Var v) acc = (if MEM v acc then acc else v::acc) ∧
  all_vars (Not x) acc = all_vars x acc ∧
  all_vars (Or x y) acc = all_vars x (all_vars y acc) ∧
  all_vars (And x y) acc = all_vars x (all_vars y acc) ∧
  all_vars (If v x y) acc = all_vars x (all_vars y (if MEM v acc then acc else v::acc))
End

Definition vars_of_def:
  vars_of xs = FOLDR all_vars [] xs
End

Definition b2n_def[simp]:
  b2n T = 1n ∧ b2n F = 0
End

Definition gol_def:
  gol x1 x2 x3
      y1 y2 y3
      z1 z2 z3
  ⇔
    let n = SUM (MAP b2n [x1;x2;x3;y1;y3;z1;z2;z3]) in
      n = 3 ∨ (y2 ∧ n = 2)
End

Definition eval_bool_exp_def:
  eval_bool_exp True true_vars = T ∧
  eval_bool_exp False true_vars = F ∧
  eval_bool_exp (Var v) true_vars = MEM v true_vars ∧
  eval_bool_exp (Not x) true_vars = ~ eval_bool_exp x true_vars ∧
  eval_bool_exp (Or x y) true_vars =
    (eval_bool_exp x true_vars ∨ eval_bool_exp y true_vars) ∧
  eval_bool_exp (And x y) true_vars =
    (eval_bool_exp x true_vars ∧ eval_bool_exp y true_vars) ∧
  eval_bool_exp (If v x y) true_vars =
    if MEM v true_vars then eval_bool_exp x true_vars else eval_bool_exp y true_vars
End

Definition sum_bool_exps_def:
  sum_bool_exps [] true_vars = 0:num ∧
  sum_bool_exps (e::es) true_vars =
    if eval_bool_exp e true_vars then 1 + sum_bool_exps es true_vars
    else sum_bool_exps es true_vars
End

Definition decide_gol_def:
  (decide_gol (v::vs) y2 rest true_vars =
    SmartIf v (decide_gol vs y2 rest (v::true_vars))
              (decide_gol vs y2 rest true_vars)) ∧
  (decide_gol [] y2 rest true_vars =
    let n = sum_bool_exps rest true_vars in
      if n = 3 then True else
        if eval_bool_exp y2 true_vars ∧ n = 2 then True else False)
End

Definition is_eq_def:
  (is_eq (v::vs) e1 e2 true_vars =
     (is_eq vs e1 e2 (v::true_vars) ∧ is_eq vs e1 e2 true_vars)) ∧
  (is_eq [] e1 e2 true_vars =
     (eval_bool_exp e1 true_vars = eval_bool_exp e2 true_vars))
End

Definition is_eq_bool_exp_def:
  is_eq_bool_exp e1 e2 =
    let vs = all_vars e1 (all_vars e2 []) in
      is_eq vs e1 e2 []
End

Definition bool_exp_gol_def:
  bool_exp_gol x1 x2 x3
               y1 y2 y3
               z1 z2 z3
  =
  let vs = vars_of [x1;x2;x3;y1;y2;y3;z1;z2;z3] in
    decide_gol vs y2 [x1;x2;x3;y1;y3;z1;z2;z3] []
End

val bool_exp_gol_eq = bool_exp_gol_def
  |> SIMP_RULE std_ss [vars_of_def,listTheory.FOLDR];

(*

time EVAL “bool_exp_gol False False False
      (Var (A 1)) False (Var (A 1))
      (Var (A 1)) False (Var (B 1))”

*)

val res = cv_trans eval_bool_exp_def
val res = cv_trans sum_bool_exps_def
val res = cv_trans SmartIf_def
val res = cv_trans decide_gol_def
val res = cv_trans all_vars_def
val res = cv_trans bool_exp_gol_eq
val res = cv_trans is_eq_def
val res = cv_trans is_eq_bool_exp_def

val res = cv_eval “bool_exp_gol False       (Var (B 1)) False
                                (Var (A 1)) False       (Var (A 2))
                                (Var (A 1)) False       (Var (B 1))”

val res = cv_eval “is_eq_bool_exp False (Or (Var (A 1)) (Not (Var (A 1))))”
val res = cv_eval “is_eq_bool_exp (And (Var (A 1)) (Var (B 1))) (And (Var (B 1)) (Var (A 1)))”

Definition next_row_def:
  (next_row (x1::x2::x3::xs) (y1::y2::y3::ys) (z1::z2::z3::zs) ⇔
     bool_exp_gol x1 x2 x3 y1 y2 y3 z1 z2 z3 ::
     next_row (x2::x3::xs) (y2::y3::ys) (z2::z3::zs)) ∧
  (next_row (x1::x2::[]) (y1::y2::[]) (z1::z2::[]) ⇔
     bool_exp_gol x1 x2 False y1 y2 False z1 z2 False :: []) ∧
  (next_row _ _ _ ⇔ [])
End

Definition next_frame_def:
  (next_frame (x::y::z::xs) ⇔
     next_row (False :: x) (False :: y) (False :: z) ::
     next_frame (y::z::xs)) ∧
  (next_frame (x::y::[]) ⇔
     next_row (False :: x) (False :: y) (False :: MAP (K False) y) :: []) ∧
  (next_frame _ ⇔ [])
End

Definition next_sim_def:
  next_sim [] = [] ∧
  next_sim (x::xs) = next_frame (MAP (K False) x :: x :: xs)
End

val res = cv_trans next_row_def
val res = cv_auto_trans next_frame_def
val res = cv_trans next_sim_def

val res = cv_eval “next_sim [[False; Var (A 1); False];
                             [Var (A 1); Var (A 1);  Var (B 1)];
                             [False; Var (A 1); False]]”

val _ = export_theory();
