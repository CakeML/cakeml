(*
   Fast interpreter function for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory compute_syntaxTheory
     compute_evalTheory;
open ml_monadBaseTheory ml_monadBaseLib;
open mlvectorTheory

val _ = new_theory "compute_exec";

(* -------------------------------------------------------------------------
 * st_ex_monad setup
 * ------------------------------------------------------------------------- *)

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = SOME “raise_Failure”,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

Overload return[local] = “st_ex_return”;
Overload failwith[local] = “raise_Failure”;
Overload handle[local] = “handle_Failure”;
Overload error[local] = “raise_Failure «error»”;
Overload timeout[local] = “raise_Failure «timeout»”;

(* -------------------------------------------------------------------------
 * execute engine
 * ------------------------------------------------------------------------- *)

Datatype:
  cv = Num num | Pair cv cv
End

Datatype:
  ce = Const num
     | Var num
     | Monop (cv -> cv) ce
     | Binop (cv -> cv -> cv) ce ce
     | App num (ce list)
     | If ce ce ce
     | Let ce ce
End

Definition env_lookup_def:
  env_lookup n [] = Num 0 /\
  env_lookup n (x::xs) =
    if n = 0n then x else env_lookup (n-1) xs
End

Definition get_code_def:
  get_code f funs =
    if f < length funs then
      return (sub funs f)
    else
      timeout
End

Definition exec_def:
  exec funs env ck (Const n) =
    return (Num n) ∧
  exec funs env ck (Var n) =
    return (env_lookup n env) ∧
  exec funs env ck (Monop m x) =
    do
      v <- exec funs env ck x;
      return (m v)
    od ∧
  exec funs env ck (Binop b x y) =
    do
      v <- exec funs env ck x;
      w <- exec funs env ck y;
      return (b v w)
    od ∧
  exec funs env ck (App f xs) =
    (if ck = 0 then timeout else
    do
      vs <- exec_list funs env ck xs [];
      c <- get_code f funs;
      exec funs vs (ck-1n) c
    od) ∧
  exec funs env ck (Let x y) =
    (if ck = 0 then timeout else
    do
      v <- exec funs env ck x;
      exec funs (v::env) (ck-1) y
    od) ∧
  exec funs env ck (If x y z) =
    do
      v <- exec funs env ck x;
      exec funs env ck (if v = Num 0 then z else y)
    od ∧
  exec_list funs env ck [] acc =
    return acc ∧
  exec_list funs env ck (x::xs) acc =
    do
      v <- exec funs env ck x;
      exec_list funs env ck xs (v::acc)
    od
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) $
              λx. case x of INL (_,_,ck,cv) => (ck, ce_size cv)
                          | INR (_,_,ck,cv,_) => (ck, ce1_size cv)’
  \\ rw [] \\ fs []
End

Definition monop_def:
  (monop Fst    = λx. case x of Pair y z => y | _ => Num 0) ∧
  (monop Snd    = λx. case x of Pair y z => z | _ => Num 0) ∧
  (monop IsPair = λx. case x of Pair y z => Num 1 | _ => Num 0)
End

Definition to_num_def[simp]:
  to_num (Pair _ _) = 0 ∧
  to_num ((Num n):cv) = n
End

Definition cv_T_def:
  cv_T = Num 1 : cv
End

Definition cv_F_def:
  cv_F = Num 0 : cv
End

Definition binop_def:
  binop op =
    case op of
    | Add => (λx y. Num (to_num x + to_num y))
    | Sub => (λx y. Num (to_num x - to_num y))
    | Mul => (λx y. Num (to_num x * to_num y))
    | Div => (λx y. Num (let k = to_num y in if k = 0 then 0 else to_num x DIV k))
    | Mod => (λx y. Num (let k = to_num y in if k = 0 then to_num x else to_num x MOD k))
    | Eq   => (λx y. if x = y then cv_T else cv_F)
    | Less => (λx y. case x of
                     | Pair _ _ => cv_F
                     | Num n    => case y of
                                   | Pair _ _ => cv_F
                                   | Num m    => if n < m then cv_T else cv_F)
End

Definition to_ce_def:
  to_ce (eqs:(mlstring # mlstring list # compute_exp) list)
    args ((Var v):compute_exp) = Var (findi v args) ∧
  to_ce eqs args (Num n) = Const n ∧
  to_ce eqs args (Pair x y) =
    Binop Pair (to_ce eqs args x) (to_ce eqs args y) ∧
  to_ce eqs args (If x y z) =
    If (to_ce eqs args x) (to_ce eqs args y) (to_ce eqs args z) ∧
  to_ce eqs args (Let s x y) =
    Let (to_ce eqs args x) (to_ce eqs (s::args) y) ∧
  to_ce eqs args (Uop m x) =
    Monop (monop m) (to_ce eqs args x) ∧
  to_ce eqs args (Binop b x y) =
    Binop (binop b) (to_ce eqs args x) (to_ce eqs args y) ∧
  to_ce eqs args (App f xs) =
    App (findi f (MAP FST eqs)) (MAP (to_ce eqs args) xs)
Termination
  WF_REL_TAC ‘measure $ λ(eqs,args,e). compute_exp_size e’
End

Definition compile_to_ce_def:
  compile_to_ce eqs (n,args,body) = to_ce eqs (REVERSE args) body
End

Definition build_funs_def:
  build_funs eqs = Vector ((MAP (compile_to_ce eqs) eqs) : ce list)
End

Definition cv2term_def:
  cv2term ((Num n):cv) = _CEXP_NUM (_NUMERAL (num2bit n)) ∧
  cv2term (Pair p q)   = _CEXP_PAIR (cv2term p) (cv2term q)
End

val _ = export_theory ();
