(*
   Definitions of term embeddings for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory;
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "compute_syntax";

val _ = numLib.prefer_num ();

(* Numbers, bools *)

Overload num_ty = “Tyapp «num» []”;

Overload "_X" = “Var «x» Bool”;
Overload "_TRUE" = “Const «T» Bool”;
Overload "_FALSE" = “Const «F» Bool”;
Overload "_NOT_TM" = “Const «~» (Fun Bool Bool)”;
Overload "_NOT" = “λtm. Comb _NOT_TM tm”;
Overload "_COND_TM" =
  “Const «COND» (Fun Bool (Fun num_ty (Fun num_ty num_ty)))”;
Overload "_COND" = “λt t1 t2. Comb (Comb (Comb _COND_TM t) t1) t2”;

Overload "_0" = “Const «_0» num_ty”;
Overload "_SUC_TM" = “Const «SUC» (Fun num_ty num_ty)”;
Overload "_SUC" = “λtm. Comb _SUC_TM tm”;
Overload "_BIT0_TM" = “Const «BIT0» (Fun num_ty num_ty)”;
Overload "_BIT0" = “λtm. Comb _BIT0_TM tm”;
Overload "_BIT1_TM" = “Const «BIT1» (Fun num_ty num_ty)”;
Overload "_BIT1" = “λtm. Comb _BIT1_TM tm”;
Overload "_N" = “Var «n» num_ty”;
Overload "_M" = “Var «m» num_ty”;
Overload "_ADD_TM" = “Const «+» (Fun num_ty (Fun num_ty num_ty))”;
Overload "_ADD" = “λt1 t2. Comb (Comb _ADD_TM t1) t2”;
Overload "_SUB_TM" = “Const «-» (Fun num_ty (Fun num_ty num_ty))”;
Overload "_SUB" = “λt1 t2. Comb (Comb _SUB_TM t1) t2”;
Overload "_MUL_TM" = “Const «*» (Fun num_ty (Fun num_ty num_ty))”;
Overload "_MUL" = “λt1 t2. Comb (Comb _MUL_TM t1) t2”;
Overload "_MOD_TM" = “Const «MOD» (Fun num_ty (Fun num_ty num_ty))”;
Overload "_MOD" = “λt1 t2. Comb (Comb _MOD_TM t1) t2”;
Overload "_DIV_TM" = “Const «DIV» (Fun num_ty (Fun num_ty num_ty))”;
Overload "_DIV" = “λt1 t2. Comb (Comb _DIV_TM t1) t2”;
Overload "_LESS_TM" = “Const «<» (Fun num_ty (Fun num_ty Bool))”;
Overload "_LESS" = “λt1 t2. Comb (Comb _LESS_TM t1) t2”;
Overload "_NUMERAL_TM" = “Const «NUMERAL» (Fun num_ty num_ty)”;
Overload "_NUMERAL" = “λtm. Comb _NUMERAL_TM tm”;

(* Pairs *)

Overload cval_ty = “Tyapp «cval» []”;
Overload cval_list_ty = “Tyapp «list» [cval_ty]”;
Overload "_P1" = “Var «p1» cval_ty”;
Overload "_P2" = “Var «p2» cval_ty”;
Overload "_Q1" = “Var «q1» cval_ty”;
Overload "_Q2" = “Var «q2» cval_ty”;
Overload "_CS" = “Var «cs» cval_list_ty”;
Overload "_CVAL_NIL_TM" = “Const «[]» cval_list_ty”;
Overload "_CVAL_CONS_TM" =
  “Const «::» (Fun cval_ty (Fun cval_list_ty cval_list_ty))”;
Overload "_CVAL_CONS" = “λt1 t2. Comb (Comb _CVAL_CONS_TM t1) t2”;
Overload "_CVAL_NUM_TM" = “Const «cval_num» (Fun num_ty cval_ty)”;
Overload "_CVAL_NUM" = “λtm. Comb _CVAL_NUM_TM tm”;
Overload "_CVAL_PAIR_TM" =
  “Const «cval_pair» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_PAIR" = “λt1 t2. Comb (Comb _CVAL_PAIR_TM t1) t2”;
Overload "_CVAL_VAR_TM" = “Const «cval_var» (Fun string_ty cval_ty)”
Overload "_CVAL_VAR" = “λtm. Comb _CVAL_VAR_TM tm”
Overload "_CVAL_ADD_TM" =
  “Const «cval_add» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_ADD" = “λt1 t2. Comb (Comb _CVAL_ADD_TM t1) t2”;
Overload "_CVAL_SUB_TM" =
  “Const «cval_sub» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_SUB" = “λt1 t2. Comb (Comb _CVAL_SUB_TM t1) t2”;
Overload "_CVAL_MUL_TM" =
  “Const «cval_mul» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_MUL" = “λt1 t2. Comb (Comb _CVAL_MUL_TM t1) t2”;
Overload "_CVAL_MOD_TM" =
  “Const «cval_mod» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_MOD" = “λt1 t2. Comb (Comb _CVAL_MOD_TM t1) t2”;
Overload "_CVAL_DIV_TM" =
  “Const «cval_div» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_DIV" = “λt1 t2. Comb (Comb _CVAL_DIV_TM t1) t2”;
Overload "_CVAL_LESS_TM" =
  “Const «cval_less» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_LESS" = “λt1 t2. Comb (Comb _CVAL_LESS_TM t1) t2”;
Overload "_CVAL_APP_TM" =
  “Const «cval_app» (Fun string_ty (Fun cval_list_ty cval_ty))”;
Overload "_CVAL_APP" = “λt1 t2. Comb (Comb _CVAL_APP_TM t1) t2”;
Overload "_CVAL_IF_TM" =
  “Const «cval_if» (Fun cval_ty (Fun cval_ty (Fun cval_ty cval_ty)))”;
Overload "_CVAL_IF" = “λt1 t2 t3. Comb (Comb (Comb _CVAL_IF_TM t1) t2) t3”;
Overload "_CVAL_FST_TM" = “Const «cval_fst» (Fun cval_ty cval_ty)”;
Overload "_CVAL_FST" = “λtm. Comb _CVAL_FST_TM tm”;
Overload "_CVAL_SND_TM" = “Const «cval_snd» (Fun cval_ty cval_ty)”;
Overload "_CVAL_SND" = “λtm. Comb _CVAL_SND_TM tm”;

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
 * Compute values
 * ------------------------------------------------------------------------- *)

Datatype:
  binop = Add | Sub | Mul | Div | Mod | Less
End

Datatype:
  compute_val = Pair compute_val compute_val
              | Num num
              | Var mlstring
              | App mlstring (compute_val list)
              | If compute_val compute_val compute_val
                (* operations that rely on host-language features *)
              | Fst compute_val
              | Snd compute_val
              | Binop binop compute_val compute_val
End

Definition app_type_def:
  app_type arity = FUNPOW (Fun cval_ty) arity cval_ty
End

Theorem app_type:
  app_type 0 = cval_ty ∧
  app_type (SUC n) = Fun cval_ty (app_type n)
Proof
  rw [app_type_def, FUNPOW_SUC]
QED

Definition bop2term_def:
  bop2term Add = _CVAL_ADD ∧
  bop2term Sub = _CVAL_SUB ∧
  bop2term Mul = _CVAL_MUL ∧
  bop2term Div = _CVAL_DIV ∧
  bop2term Mod = _CVAL_MOD ∧
  bop2term Less = _CVAL_LESS
End

Definition cval2term_def:
  cval2term (Num n) = _CVAL_NUM (_NUMERAL (num2bit n)) ∧
  cval2term (Pair p q) = _CVAL_PAIR (cval2term p) (cval2term q) ∧
  cval2term (Fst p) = _CVAL_FST (cval2term p) ∧
  cval2term (Snd p) = _CVAL_SND (cval2term p) ∧
  cval2term (Binop bop p q) =  bop2term bop (cval2term p) (cval2term q) ∧
  cval2term (If p q r) = _CVAL_IF (cval2term p) (cval2term q) (cval2term r) ∧
  cval2term (Var s) = Var s cval_ty ∧
  cval2term (App s cs) =
    FOLDL Comb (Const s (app_type (LENGTH cs))) (MAP cval2term cs)
Termination
  wf_rel_tac ‘measure compute_val_size’
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

