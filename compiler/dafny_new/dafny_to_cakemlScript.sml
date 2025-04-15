(*
  Defines the translation of Dafny's to CakeML's AST.
*)

open preamble
open cfTacticsLib  (* process_topdecs *)
open dafny_astTheory
open astTheory  (* CakeML AST *)
open mlintTheory  (* fromString *)
open result_monadTheory

val _ = new_theory "dafny_to_cakeml";

(* General helpers *)

Definition int_to_string_def:
  int_to_string (i: int) = explode (toString i)
End

Definition num_to_string_def:
  num_to_string (n: num) = int_to_string (&n)
End

(* Helpers to generate CakeML *)

(* Shortcuts to some constructors *)
Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload Unit = “Con NONE []”

Definition cml_deref_def[simp]:
  cml_deref v = App Opderef [Var (Short (explode v))]
End

Definition cml_fapp_aux_def:
  cml_fapp_aux id cml_es =
  (case cml_es of
   | [] => App Opapp [id; Unit]
   | [cml_e] => App Opapp [id; cml_e]
   | (cml_e::rest) => App Opapp [(cml_fapp_aux id rest); cml_e])
End

Definition cml_fapp_def:
  cml_fapp mns n cml_es = cml_fapp_aux (Var (mk_id mns n)) (REVERSE cml_es)
End

(* Returns the tuple content at idx via pattern matching *)
Definition cml_tuple_select_def:
  cml_tuple_select len cml_te (idx: num) =
  let field_vars = GENLIST (λn. Pvar ("_" ++ (num_to_string n))) len in
    Mat cml_te [Pcon NONE field_vars, Var (Short ("t" ++ (num_to_string idx)))]
End

(* Dafny to CakeML definitions *)

Definition from_lit_def:
  from_lit l =
  (case l of
   | BoolL b => if b then True else False
   | IntL i => Lit (IntLit i)
   | StrL s => Lit (StrLit (explode s)))
End

Definition from_un_op_def:
  from_un_op uop cml_e =
  (case uop of
   | Not => cml_fapp [] "not" [cml_e])
End

Definition from_bin_op_def:
  from_bin_op bop cml_e₀ cml_e₁ =
  (case bop of
   | Lt => App (Opb Lt) [cml_e₀; cml_e₁]
   | Le => App (Opb Leq) [cml_e₀; cml_e₁]
   | Ge => App (Opb Geq) [cml_e₀; cml_e₁]
   | Eq => App Equality [cml_e₀; cml_e₁]
   | Neq => (let eq = from_bin_op Eq cml_e₀ cml_e₁ in from_un_op Not eq)
   | Sub => App (Opn Minus) [cml_e₀; cml_e₁]
   | Add => App (Opn Plus) [cml_e₀; cml_e₁]
   | Mul => App (Opn Times) [cml_e₀; cml_e₁]
   | And => Log And cml_e₀ cml_e₁
   | Or => Log Or cml_e₀ cml_e₁
   | Imp =>
     (let not_e₀ = from_un_op Not cml_e₀ in from_bin_op Or not_e₀ cml_e₁)
   | Div => cml_fapp ["Dafny"] "ediv" [cml_e₀; cml_e₁])
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | (Neq, _, _) => bin_op_size Neq + 1
                           | (Imp, _, _) => bin_op_size Imp + 1
                           | (bop, _, _) => bin_op_size bop)’
End

(* We model Dafny's arrays as a tuple: (length, array). This is closer to what
   we need, if we support multi-dimensional arrays. Why? In Dafny, it is
   possible to have arrays where some dimensions have length zero. At the same
   time, it is always possible to ask the length of all dimensions. Hence,
   we cannot just index to the appropriate dimension, and then use Array.length
   - we might get blocked by a dimension with length zero on the way. *)

Definition cml_get_arr_dim_def:
  cml_get_arr_dim cml_e = cml_tuple_select 2 cml_e 0
End

Definition cml_get_arr_data_def:
  cml_get_arr_data cml_e = cml_tuple_select 2 cml_e 1
End

Definition cml_arr_sel_def:
  cml_arr_sel cml_arr cml_idx =
  cml_fapp ["Array"] "sub" [cml_get_arr_data cml_arr; cml_idx]
End

Definition from_exp_def:
  from_exp e =
  (let here = extend_path «» «from_exp» in
   (case e of
    | Lit l => return (from_lit l)
    | Var v => return (cml_deref v)
    | If tst thn els =>
      do
        cml_tst <- prefix_error here (from_exp tst);
        cml_thn <- prefix_error here (from_exp thn);
        cml_els <- prefix_error here (from_exp els);
        return (If cml_tst cml_thn cml_els)
      od
    | UnOp uop e =>
      do
        cml_e <- prefix_error here (from_exp e);
        return (from_un_op uop cml_e)
      od
    | BinOp bop e₀ e₁ =>
      do
        cml_e₀ <- prefix_error here (from_exp e₀);
        cml_e₁ <- prefix_error here (from_exp e₁);
        return (from_bin_op bop cml_e₀ cml_e₁)
      od
    | ArrLen arr =>
      do
        cml_arr <- prefix_error here (from_exp arr);
        return (cml_get_arr_dim cml_arr)
      od
    | ArrSel arr idx =>
      do
        cml_arr <- prefix_error here (from_exp arr);
        cml_idx <- prefix_error here (from_exp idx);
        return (cml_arr_sel cml_arr cml_idx)
      od
    | FunCall name args =>
      do
        cml_args <- prefix_error here (from_exps args);
        return (cml_fapp [] (explode name) cml_args)
      od
    | Forall _ _ => fail ((extend_path here «Forall») ^ « Unsupported»))) ∧
  from_exps es =
  (case es of
   | [] => return []
   | (e::es) =>
     do
       cml_e <- from_exp e;
       cml_es <- from_exps es;
       return (cml_e::cml_es)
     od)
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL e => exp_size e
                           | INR es => list_size exp_size es)’
End

(* Defines the Dafny module containing the Dafny runtime *)

Quote dafny_module = process_topdecs:
  (* Adapted from ABS and ediv from HOL's integerTheory *)
  fun abs n = if n < 0 then ~n else n;

  fun ediv i j = if 0 < j then i div j else ~(i div ~j);
End

val _ = export_theory ();
