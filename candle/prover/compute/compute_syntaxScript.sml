(*
   Definitions of 'compute expressions' for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory;

val _ = new_theory "compute_syntax";

val _ = numLib.prefer_num ();

(* Numbers, bools *)

Overload Num = “Tyapp «num» []”;

Overload "_X" = “Var «x» Bool”;
Overload "_Y" = “Var «y» Bool”;
Overload "_TRUE" = “Const «T» Bool”;
Overload "_FALSE" = “Const «F» Bool”;
(* COND on numbers: *)
Overload "_COND_TM" =
  “Const «COND» (Fun Bool (Fun Num (Fun Num Num)))”;
Overload "_COND" = “λt t1 t2. Comb (Comb (Comb _COND_TM t) t1) t2”;
(* COND on booleans: *)
Overload "_IF_TM" =
  “Const «COND» (Fun Bool (Fun Bool (Fun Bool Bool)))”;
Overload "_IF" = “λt t1 t2. Comb (Comb (Comb _IF_TM t) t1) t2”;

Overload "_0" = “Const «_0» Num”;
Overload "_SUC_TM" = “Const «SUC» (Fun Num Num)”;
Overload "_SUC" = “λtm. Comb _SUC_TM tm”;
Overload "_BIT0_TM" = “Const «BIT0» (Fun Num Num)”;
Overload "_BIT0" = “λtm. Comb _BIT0_TM tm”;
Overload "_BIT1_TM" = “Const «BIT1» (Fun Num Num)”;
Overload "_BIT1" = “λtm. Comb _BIT1_TM tm”;
Overload "_N" = “Var «n» Num”;
Overload "_M" = “Var «m» Num”;
Overload "_ADD_TM" = “Const «+» (Fun Num (Fun Num Num))”;
Overload "_ADD" = “λt1 t2. Comb (Comb _ADD_TM t1) t2”;
Overload "_SUB_TM" = “Const «-» (Fun Num (Fun Num Num))”;
Overload "_SUB" = “λt1 t2. Comb (Comb _SUB_TM t1) t2”;
Overload "_MUL_TM" = “Const «*» (Fun Num (Fun Num Num))”;
Overload "_MUL" = “λt1 t2. Comb (Comb _MUL_TM t1) t2”;
Overload "_MOD_TM" = “Const «MOD» (Fun Num (Fun Num Num))”;
Overload "_MOD" = “λt1 t2. Comb (Comb _MOD_TM t1) t2”;
Overload "_DIV_TM" = “Const «DIV» (Fun Num (Fun Num Num))”;
Overload "_DIV" = “λt1 t2. Comb (Comb _DIV_TM t1) t2”;
Overload "_LESS_TM" = “Const «<» (Fun Num (Fun Num Bool))”;
Overload "_LESS" = “λt1 t2. Comb (Comb _LESS_TM t1) t2”;
Overload "_NUMERAL_TM" = “Const «NUMERAL» (Fun Num Num)”;
Overload "_NUMERAL" = “λtm. Comb _NUMERAL_TM tm”;

(* Compute expressions *)

Overload Cexp = “Tyapp «cval» []”;
Overload Cexp_list = “Tyapp «list» [Cexp]”;
Overload "_P1" = “Var «p1» Cexp”;
Overload "_P2" = “Var «p2» Cexp”;
Overload "_Q1" = “Var «q1» Cexp”;
Overload "_Q2" = “Var «q2» Cexp”;
Overload "_CS" = “Var «cs» Cexp_list”;
(*
Overload "_CEXP_NIL_TM" = “Const «[]» Cexp_list”;
Overload "_CEXP_CONS_TM" =
  “Const «::» (Fun Cexp (Fun Cexp_list Cexp_list))”;
Overload "_CEXP_CONS" = “λt1 t2. Comb (Comb _CEXP_CONS_TM t1) t2”;
 *)
Overload "_CEXP_NUM_TM" = “Const «Cexp_num» (Fun Num Cexp)”;
Overload "_CEXP_NUM" = “λtm. Comb _CEXP_NUM_TM tm”;
Overload "_CEXP_PAIR_TM" = “Const «Cexp_pair» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_PAIR" = “λt1 t2. Comb (Comb _CEXP_PAIR_TM t1) t2”;

Overload "_CEXP_VAR_TM" = “Const «Cexp_var» (Fun string_ty Cexp)”
Overload "_CEXP_VAR" = “λtm. Comb _CEXP_VAR_TM tm”
Overload "_CEXP_ADD_TM" =
  “Const «Cexp_add» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_ADD" = “λt1 t2. Comb (Comb _CEXP_ADD_TM t1) t2”;
Overload "_CEXP_SUB_TM" =
  “Const «Cexp_sub» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_SUB" = “λt1 t2. Comb (Comb _CEXP_SUB_TM t1) t2”;
Overload "_CEXP_MUL_TM" =
  “Const «Cexp_mul» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_MUL" = “λt1 t2. Comb (Comb _CEXP_MUL_TM t1) t2”;
Overload "_CEXP_MOD_TM" =
  “Const «Cexp_mod» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_MOD" = “λt1 t2. Comb (Comb _CEXP_MOD_TM t1) t2”;
Overload "_CEXP_DIV_TM" =
  “Const «Cexp_div» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_DIV" = “λt1 t2. Comb (Comb _CEXP_DIV_TM t1) t2”;
Overload "_CEXP_LESS_TM" =
  “Const «Cexp_less» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_LESS" = “λt1 t2. Comb (Comb _CEXP_LESS_TM t1) t2”;
Overload "_CEXP_APP_TM" =
  “Const «Cexp_app» (Fun string_ty (Fun Cexp_list Cexp))”;
Overload "_CEXP_APP" = “λt1 t2. Comb (Comb _CEXP_APP_TM t1) t2”;
Overload "_CEXP_IF_TM" =
  “Const «Cexp_if» (Fun Cexp (Fun Cexp (Fun Cexp Cexp)))”;
Overload "_CEXP_IF" = “λt1 t2 t3. Comb (Comb (Comb _CEXP_IF_TM t1) t2) t3”;
Overload "_CEXP_FST_TM" = “Const «Cexp_fst» (Fun Cexp Cexp)”;
Overload "_CEXP_FST" = “λtm. Comb _CEXP_FST_TM tm”;
Overload "_CEXP_SND_TM" = “Const «Cexp_snd» (Fun Cexp Cexp)”;
Overload "_CEXP_SND" = “λtm. Comb _CEXP_SND_TM tm”;
Overload "_CEXP_ISPAIR_TM" = “Const «Cexp_ispair» (Fun Cexp Cexp)”;
Overload "_CEXP_ISPAIR" = “λtm. Comb _CEXP_ISPAIR_TM tm”;
Overload "_CEXP_EQ_TM" = “Const «Cexp_eq» (Fun Cexp (Fun Cexp Cexp))”;
Overload "_CEXP_EQ" = “λt1 t2. Comb (Comb _CEXP_EQ_TM t1) t2”;

(* Lets, “let a = b in x”: *)

Overload "_F" = “Var «f» (Fun Cexp Cexp)”;
Overload "_LET_TM" = “Const «LET» (Fun (Fun Cexp Cexp) (Fun Cexp Cexp))”;
Overload "_LET" = “λt1 t2. Comb (Comb _LET_TM t1) t2”;

(* -------------------------------------------------------------------------
 * Bools
 * ------------------------------------------------------------------------- *)

Definition bool2term_def:
  bool2term F = _FALSE ∧
  bool2term T = _TRUE
End

(* -------------------------------------------------------------------------
 * Natural numbers
 * ------------------------------------------------------------------------- *)

Definition num2term_def:
  num2term 0 = _0 ∧
  num2term (SUC n) = _SUC (num2term n)
End

Definition num2bit_def:
  num2bit n =
    if n = 0 then _0 else
    Comb (if n MOD 2 = 0 then _BIT0_TM else _BIT1_TM) (num2bit (n DIV 2))
Termination
  wf_rel_tac ‘$<’ \\ intLib.ARITH_TAC
End

(* -------------------------------------------------------------------------
 * Compute expressions
 * ------------------------------------------------------------------------- *)

Datatype:
  binop = Add | Sub | Mul | Div | Mod | Less | Eq
End

Datatype:
  uop = Fst | Snd | Ispair
End

Datatype:
  compute_exp = Pair compute_exp compute_exp
              | Num num
              | Var mlstring
              | App mlstring (compute_exp list)
              | If compute_exp compute_exp compute_exp
              | Let mlstring compute_exp compute_exp
              | Uop uop compute_exp
              | Binop binop compute_exp compute_exp
End

Definition cexp_value_def[simp]:
  cexp_value (Num n) = T ∧
  cexp_value (Pair p q) = (cexp_value p ∧ cexp_value q) ∧
  cexp_value _ = F
End

Definition app_type_def:
  app_type arity = FUNPOW (Fun Cexp) arity Cexp
End

Theorem app_type:
  app_type 0 = Cexp ∧
  app_type (SUC n) = Fun Cexp (app_type n)
Proof
  rw [app_type_def, FUNPOW_SUC]
QED

Definition bop2term_def:
  bop2term Add = _CEXP_ADD ∧
  bop2term Sub = _CEXP_SUB ∧
  bop2term Mul = _CEXP_MUL ∧
  bop2term Div = _CEXP_DIV ∧
  bop2term Mod = _CEXP_MOD ∧
  bop2term Less = _CEXP_LESS ∧
  bop2term Eq = _CEXP_EQ
End

Definition uop2term_def:
  uop2term Fst = _CEXP_FST ∧
  uop2term Snd = _CEXP_SND ∧
  uop2term Ispair = _CEXP_ISPAIR
End

Definition cexp2term_def:
  cexp2term (Num n) = _CEXP_NUM (_NUMERAL (num2bit n)) ∧
  cexp2term (Pair p q) = _CEXP_PAIR (cexp2term p) (cexp2term q) ∧
  cexp2term (Uop uop p) = uop2term uop (cexp2term p) ∧
  cexp2term (Binop bop p q) =  bop2term bop (cexp2term p) (cexp2term q) ∧
  cexp2term (If p q r) = _CEXP_IF (cexp2term p) (cexp2term q) (cexp2term r) ∧
  cexp2term (Let s x y) = _LET (Abs (Var s Cexp) (cexp2term y)) (cexp2term x) ∧
  cexp2term (Var s) = Var s Cexp ∧
  cexp2term (App s cs) =
    FOLDL Comb (Const s (app_type (LENGTH cs))) (MAP cexp2term cs)
Termination
  wf_rel_tac ‘measure compute_exp_size’
End

(* DIV and MOD definitions that are defined for zero (and as in HOL Light). *)

Definition SAFEDIV_def:
  SAFEDIV m n = if n = 0 then 0 else m DIV n
End

val _ = Parse.add_infix ("SAFEDIV", 500, HOLgrammars.LEFT);

Definition SAFEMOD_def:
  SAFEMOD m n = if n = 0 then m else m MOD n
End

val _ = Parse.add_infix ("SAFEMOD", 500, HOLgrammars.LEFT);

val _ = export_theory ();
